import LeanBiscuit.Token.Biscuit
import LeanBiscuit.Parser

/-!
# Authorization

The authorizer is the context a token is evaluated in.  It supplies the facts
about the request being made — the resource, the operation, the current time —
along with its own checks and the allow/deny policies that decide the outcome.

Authorization proceeds in a fixed order: load the token's blocks into a datalog
world, run the engine to a fixpoint, evaluate the authorizer's checks, then the
authority block's checks, then the policies, then the remaining blocks' checks.
The result is the index of the `allow` policy that matched — but only if no
check failed.
-/

namespace LeanBiscuit
namespace Token

open Datalog Builder

/-- An authorizer ready to be run against a token. -/
structure Authorizer where
  /-- The datalog world, holding the token's facts and rules. -/
  world : World := {}
  /-- The authorizer's symbol table, into which the token's blocks were
  translated. -/
  symbols : SymbolTable := {}
  /-- The token's blocks, translated into the authorizer's symbol table. -/
  blocks : Option (List Block) := none
  /-- Which blocks each public key of the table signed. -/
  publicKeyToBlockId : List (Nat × List Nat) := []
  /-- Facts the authorizer states about the request. -/
  facts : List Builder.Fact := []
  /-- Rules the authorizer adds. -/
  rules : List Builder.Rule := []
  /-- Checks the authorizer imposes. -/
  checks : List Builder.Check := []
  /-- The authorizer's own trust annotation. -/
  scopes : List Builder.Scope := []
  /-- The policies that decide the outcome. -/
  policies : List Builder.Policy := []
  /-- Host functions callable from datalog. -/
  externs : Externs := []
  /-- The datalog engine's runtime limits. -/
  limits : RunLimits := {}
  deriving Inhabited

/-- What an authorizer is built from before it sees a token. -/
structure AuthorizerBuilder where
  /-- Facts about the request. -/
  facts : List Builder.Fact := []
  /-- Rules to add. -/
  rules : List Builder.Rule := []
  /-- Checks to impose. -/
  checks : List Builder.Check := []
  /-- The authorizer's trust annotation. -/
  scopes : List Builder.Scope := []
  /-- The policies. -/
  policies : List Builder.Policy := []
  /-- Host functions. -/
  externs : Externs := []
  /-- Runtime limits. -/
  limits : RunLimits := {}
  deriving Inhabited

namespace AuthorizerBuilder

/-- Add the contents of a datalog source string. -/
def code (b : AuthorizerBuilder) (source : String) : Except TokenError AuthorizerBuilder :=
  match Parser.parseAuthorizer source with
  | .error e => throw (.language e)
  | .ok r =>
    pure { b with
      facts := b.facts ++ r.facts,
      rules := b.rules ++ r.rules,
      checks := b.checks ++ r.checks,
      policies := b.policies ++ r.policies }

/-- Register the host functions datalog may call. -/
def withExterns (b : AuthorizerBuilder) (externs : Externs) : AuthorizerBuilder :=
  { b with externs }

end AuthorizerBuilder

namespace Authorizer

/-- Load one block into the world, translating it into the authorizer's symbol
table.

A third-party block is interpreted with its own symbol table: whoever signed it
did not have the token, so its symbol indices are its own. -/
def loadBlock (a : Authorizer) (tokenSymbols : SymbolTable) (index : Nat) (block : Block) :
    Except TokenError (Authorizer × Block) := do
  let blockSymbols :=
    if index == 0 || block.externalKey.isNone then tokenSymbols else block.symbols
  let mut symbols := a.symbols
  let mut world := a.world
  let blockOrigin : Origin := Origin.empty.insert index
  -- translate the block-level trust annotation
  let mut scopes : List Datalog.Scope := []
  for s in block.scopes do
    let bs ← liftM ((Builder.Scope.convertFrom blockSymbols s).mapError TokenError.format)
    let (s, t) := Builder.Scope.convert symbols bs
    symbols := t
    scopes := scopes ++ [s]
  let blockTrusted := TrustedOrigins.fromScopes scopes TrustedOrigins.default index
    a.publicKeyToBlockId
  let mut facts : List Datalog.Fact := []
  for f in block.facts do
    let bf ← liftM ((Builder.Fact.convertFrom blockSymbols f).mapError TokenError.format)
    let (f, t) := Builder.Fact.convert symbols bf
    symbols := t
    facts := facts ++ [f]
    world := world.addFact blockOrigin f
  let mut rules : List Datalog.Rule := []
  for r in block.rules do
    -- a rule whose head has an unbound variable could produce arbitrary facts
    if !r.unboundHeadVariables.isEmpty then
      throw (.failedLogic (.invalidBlockRule 0 (printRule blockSymbols r)))
    let br ← liftM ((Builder.Rule.convertFrom blockSymbols r).mapError TokenError.format)
    let (r, t) := Builder.Rule.convert symbols br
    symbols := t
    let ruleTrusted := TrustedOrigins.fromScopes r.scopes blockTrusted index a.publicKeyToBlockId
    world := world.addRule index ruleTrusted r
    rules := rules ++ [r]
  let mut checks : List Datalog.Check := []
  for c in block.checks do
    let bc ← liftM ((Builder.Check.convertFrom blockSymbols c).mapError TokenError.format)
    let (c, t) := Builder.Check.convert symbols bc
    symbols := t
    checks := checks ++ [c]
  pure ({ a with symbols, world },
        { block with scopes, facts, rules, checks })

/-- Build an authorizer for a token. -/
def build (b : AuthorizerBuilder) (token : Biscuit) : Except TokenError Authorizer := do
  let mut a : Authorizer :=
    { facts := b.facts, rules := b.rules, checks := b.checks, scopes := b.scopes,
      policies := b.policies, externs := b.externs, limits := b.limits }
  -- record which blocks each third party signed, so that `trusting <key>` can
  -- be resolved to a set of block ids
  for (sb, i) in token.container.blocks.zipIdx do
    match sb.externalSignature with
    | none => pure ()
    | some e =>
      let (keyId, symbols) := a.symbols.insertKey e.publicKey
      let existing := (a.publicKeyToBlockId.find? (fun (k, _) => k == keyId)).map (·.2) |>.getD []
      a := { a with
        symbols,
        publicKeyToBlockId :=
          a.publicKeyToBlockId.filter (fun (k, _) => k != keyId) ++ [(keyId, existing ++ [i + 1])] }
  let mut blocks : List Block := []
  for (block, i) in token.blocks.zipIdx do
    let (a', block) ← a.loadBlock token.symbols i block
    a := a'
    blocks := blocks ++ [block]
  a := { a with blocks := some blocks }
  -- the authorizer's own facts and rules
  let authorizerOrigin : Origin := Origin.empty.insert authorizerBlockId
  let mut symbols := a.symbols
  let mut scopes : List Datalog.Scope := []
  for s in a.scopes do
    let (s, t) := Builder.Scope.convert symbols s
    symbols := t
    scopes := scopes ++ [s]
  let authorizerTrusted := TrustedOrigins.fromScopes scopes TrustedOrigins.default
    authorizerBlockId a.publicKeyToBlockId
  let mut world := a.world
  for f in a.facts do
    let (f, t) := Builder.Fact.convert symbols f
    symbols := t
    world := world.addFact authorizerOrigin f
  for r in a.rules do
    let (r, t) := Builder.Rule.convert symbols r
    symbols := t
    let ruleTrusted := TrustedOrigins.fromScopes r.scopes authorizerTrusted authorizerBlockId
      a.publicKeyToBlockId
    world := world.addRule authorizerBlockId ruleTrusted r
  pure { a with symbols, world }

/-- Run one check, in whichever flavour it was written. -/
def runCheck (a : Authorizer) (kind : CheckKind) (query : Datalog.Rule)
    (trusted : TrustedOrigins) : Except ExecutionError Bool := do
  match kind with
  | .one => a.world.queryMatch a.externs a.symbols query trusted
  | .all => a.world.queryMatchAll a.externs a.symbols query trusted
  | .reject => do pure !(← a.world.queryMatch a.externs a.symbols query trusted)

/-- Does any of a check's queries succeed? -/
def checkSucceeds (a : Authorizer) (c : Datalog.Check) (defaultTrusted : TrustedOrigins)
    (currentBlock : Nat) : Except ExecutionError Bool := do
  let rec go (queries : List Datalog.Rule) : Except ExecutionError Bool := do
    match queries with
    | [] => pure false
    | q :: rest =>
      let trusted := TrustedOrigins.fromScopes q.scopes defaultTrusted currentBlock
        a.publicKeyToBlockId
      if ← a.runCheck c.kind q trusted then pure true else go rest
  go c.queries

/-- The outcome of authorization: the index of the policy that matched. -/
abbrev AuthorizeResult := Except TokenError Nat

/-- Authorization runs against a mutable authorizer: evaluating a check or a
policy interns the symbols it mentions, so the symbol table grows as it goes. -/
abbrev AuthM := ExceptT TokenError (StateM Authorizer)

/-- Intern a builder trust annotation into the authorizer's table. -/
def internScopes (scopes : List Builder.Scope) : AuthM (List Datalog.Scope) := do
  let mut out : List Datalog.Scope := []
  for sc in scopes do
    let a ← get
    let (sc, symbols) := Builder.Scope.convert a.symbols sc
    set { a with symbols }
    out := out ++ [sc]
  pure out

/-- Run the datalog engine to a fixpoint. -/
def runWorld : AuthM Unit := do
  let a ← get
  match World.run a.externs a.symbols a.limits a.world with
  | .error e => throw e.toTokenError
  | .ok world => set { a with world }

/-- Evaluate checks and policies, in the order the specification prescribes.

Every check is evaluated even after one has failed, so that the resulting error
lists all of them: an attenuated token usually fails several at once, and
knowing which is what makes the failure diagnosable. -/
def decide : AuthM Nat := do
  let mut errors : List FailedCheck := []
  let authorizerScopes ← internScopes (← get).scopes
  let authorizerTrusted := TrustedOrigins.fromScopes authorizerScopes TrustedOrigins.default
    authorizerBlockId (← get).publicKeyToBlockId
  -- the authorizer's own checks
  for (check, i) in (← get).checks.zipIdx do
    let a ← get
    let (c, symbols) := Builder.Check.convert a.symbols check
    set { a with symbols }
    let a ← get
    match a.checkSucceeds c authorizerTrusted authorizerBlockId with
    | .error e => throw e.toTokenError
    | .ok true => pure ()
    | .ok false => errors := errors ++ [.authorizer i (printCheck a.symbols c)]
  -- the authority block's checks
  match (← get).blocks with
  | none => pure ()
  | some blocks =>
    match blocks.head? with
    | none => pure ()
    | some authority =>
      let a ← get
      let authorityTrusted := TrustedOrigins.fromScopes authority.scopes TrustedOrigins.default 0
        a.publicKeyToBlockId
      for (c, j) in authority.checks.zipIdx do
        match a.checkSucceeds c authorityTrusted 0 with
        | .error e => throw e.toTokenError
        | .ok true => pure ()
        | .ok false => errors := errors ++ [.block 0 j (printCheck a.symbols c)]
  -- the policies, tested in order until one matches
  let mut policyResult : Option (Except Nat Nat) := none
  for (policy, i) in (← get).policies.zipIdx do
    if policyResult.isNone then
      let a ← get
      let (p, symbols) := Builder.Policy.convert a.symbols policy
      set { a with symbols }
      for q in p.queries do
        if policyResult.isNone then
          let a ← get
          let trusted := TrustedOrigins.fromScopes q.scopes authorizerTrusted authorizerBlockId
            a.publicKeyToBlockId
          match a.world.queryMatch a.externs a.symbols q trusted with
          | .error e => throw e.toTokenError
          | .ok false => pure ()
          | .ok true =>
            policyResult := some (match p.kind with
              | .allow => .ok i
              | .deny => .error i)
  -- the checks of the remaining blocks
  match (← get).blocks with
  | none => pure ()
  | some blocks =>
    for (block, i) in (blocks.drop 1).zipIdx do
      let a ← get
      let blockTrusted := TrustedOrigins.fromScopes block.scopes TrustedOrigins.default (i + 1)
        a.publicKeyToBlockId
      for (c, j) in block.checks.zipIdx do
        match a.checkSucceeds c blockTrusted (i + 1) with
        | .error e => throw e.toTokenError
        | .ok true => pure ()
        | .ok false => errors := errors ++ [.block (i + 1) j (printCheck a.symbols c)]
  match policyResult with
  | none => throw (.failedLogic (.noMatchingPolicy errors))
  | some (.ok i) =>
    if errors.isEmpty then pure i
    else throw (.failedLogic (.unauthorized (.allow i) errors))
  | some (.error i) => throw (.failedLogic (.unauthorized (.deny i) errors))

/-- Authorize, returning both the decision and the authorizer state it was
reached in, which carries the world that was built. -/
def authorizeWithState (a : Authorizer) : AuthorizeResult × Authorizer :=
  (do runWorld; decide).run.run a

/-- Authorize a token: run the datalog engine, then evaluate checks and
policies. -/
def authorize (a : Authorizer) : AuthorizeResult := (authorizeWithState a).1

/-! ## Inspecting the world -/

/-- A snapshot of everything an authorizer knows, rendered as datalog source.

Facts are grouped by origin, with `none` standing for the authorizer itself;
rules and checks are grouped by the block that declared them.  Within each group
the entries are sorted, so that the snapshot of a given authorization is
canonical and can be compared. -/
structure WorldDump where
  /-- Facts, grouped by the set of blocks they originate from. -/
  facts : List (List (Option Nat) × List String)
  /-- Rules, grouped by the block that declared them; `none` is the
  authorizer. -/
  rules : List (Option Nat × List String)
  /-- Checks, grouped the same way. -/
  checks : List (Option Nat × List String)
  /-- The policies, in the order they will be tested. -/
  policies : List String
  deriving Repr, Inhabited

/-- Present an origin as block ids, with the authorizer as `none`. -/
def originToOptions (o : Origin) : List (Option Nat) :=
  let (auth, blocks) := o.partition (· == authorizerBlockId)
  (auth.map fun _ => none) ++ blocks.map some

/-- Ordering on presented origins: the authorizer sorts first. -/
def compareOptions : List (Option Nat) → List (Option Nat) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match a, b with
    | none, none => compareOptions as bs
    | none, some _ => .lt
    | some _, none => .gt
    | some x, some y =>
      match Ord.compare x y with
      | .eq => compareOptions as bs
      | o => o

/-- Lexicographic ordering of string lists. -/
def compareStrings : List String → List String → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match Ord.compare a b with
    | .eq => compareStrings as bs
    | o => o

/-- Everything the authorizer knows, as a canonical snapshot. -/
def dumpWorld (a : Authorizer) : WorldDump :=
  let facts := (a.world.facts.map fun (origin, fs) =>
      (originToOptions origin, (fs.map (printFact a.symbols)).mergeSort (· ≤ ·))).mergeSort
    fun x y => match compareOptions x.1 y.1 with
      | .lt => true
      | .gt => false
      | .eq => compareStrings x.2 y.2 != .gt
  let blocks := a.blocks.getD []
  let blockRules := (blocks.zipIdx.filterMap fun (b, i) =>
    if b.rules.isEmpty then none
    else some ((some i : Option Nat), (b.rules.map (printRule a.symbols)).mergeSort (· ≤ ·)))
  let blockChecks := (blocks.zipIdx.filterMap fun (b, i) =>
    if b.checks.isEmpty then none
    else some ((some i : Option Nat), (b.checks.map (printCheck a.symbols)).mergeSort (· ≤ ·)))
  -- the authorizer's own rules and checks, interned into a working copy of the
  -- symbol table so that inspection never changes the authorizer
  let (authorizerRules, symbols) := a.rules.foldl (fun (acc, t) r =>
    let (r, t) := Builder.Rule.convert t r
    (acc ++ [printRule t r], t)) (([] : List String), a.symbols)
  let (authorizerChecks, _) := a.checks.foldl (fun (acc, t) c =>
    let (c, t) := Builder.Check.convert t c
    (acc ++ [printCheck t c], t)) (([] : List String), symbols)
  { facts,
    rules := blockRules ++ (if authorizerRules.isEmpty then []
                            else [(none, authorizerRules.mergeSort (· ≤ ·))]),
    checks := blockChecks ++ (if authorizerChecks.isEmpty then []
                              else [(none, authorizerChecks.mergeSort (· ≤ ·))]),
    policies := a.policies.map Builder.Policy.print }

/-- Answer a query against the world the authorizer has built.

The query is an ordinary rule; its results are the facts it derives, which is
how a caller extracts information from a token — for instance the roles a user
was granted. -/
def query (a : Authorizer) (q : Builder.Rule) : Except TokenError (List String) := do
  let (q, symbols) := Builder.Rule.convert a.symbols q
  let trusted := TrustedOrigins.fromScopes q.scopes TrustedOrigins.default authorizerBlockId
    a.publicKeyToBlockId
  match a.world.queryRule a.externs symbols q authorizerBlockId trusted with
  | .error e => throw e.toTokenError
  | .ok facts => pure ((facts.flatMap fun (_, fs) => fs.map (printFact symbols)).mergeSort (· ≤ ·))

/-- Build an authorizer and run it in one step. -/
def authorizeToken (b : AuthorizerBuilder) (token : Biscuit) : AuthorizeResult := do
  authorize (← build b token)

end Authorizer

end Token
end LeanBiscuit
