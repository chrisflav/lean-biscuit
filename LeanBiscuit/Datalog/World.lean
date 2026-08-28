import LeanBiscuit.Datalog.Expr

/-!
# The datalog world

A world holds facts tagged with their origin — the set of blocks that had to
cooperate to produce them — and rules tagged with the origins they are allowed
to draw facts from.  Evaluation repeatedly applies every rule to the facts it
trusts until no new fact appears.

Origins are what keeps an attenuated token from regaining rights: a rule in a
later block simply cannot see facts whose origin is outside its trusted set.
-/

namespace LeanBiscuit
namespace Datalog

/-- The block id reserved for the authorizer.  The reference implementation uses
`usize::MAX`, and the value is observable in serialized worlds, so it is
reproduced here. -/
def authorizerBlockId : Nat := 18446744073709551615

/-- The set of blocks a fact came from, kept sorted and deduplicated. -/
abbrev Origin := List Nat

namespace Origin

/-- The empty origin. -/
def empty : Origin := []

/-- Add a block id. -/
def insert (o : Origin) (i : Nat) : Origin :=
  match o with
  | [] => [i]
  | x :: xs =>
    if i < x then i :: x :: xs
    else if i == x then x :: xs
    else x :: insert xs i

/-- The union of two origins. -/
def union (a b : Origin) : Origin := b.foldl (fun acc i => acc.insert i) a

/-- Does `a` contain every element of `b`? -/
def isSuperset (a b : Origin) : Bool := b.all a.contains

/-- Ordering, so that fact groups can be listed deterministically. -/
def compare (a b : Origin) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match Ord.compare x y with
    | .eq => compare xs ys
    | o => o

end Origin

/-- The origins a rule is allowed to draw facts from. -/
abbrev TrustedOrigins := Origin

namespace TrustedOrigins

/-- The default trust: the authority block and the authorizer. -/
def default : TrustedOrigins := Origin.empty.insert authorizerBlockId |>.insert 0

/-- Resolve a rule's trust annotations into a set of block ids.

With no annotation the rule inherits `defaultOrigins`; in every case the current
block and the authorizer are trusted. -/
def fromScopes (scopes : List Scope) (defaultOrigins : TrustedOrigins) (currentBlock : Nat)
    (publicKeyToBlockId : List (Nat × List Nat)) : TrustedOrigins :=
  if scopes.isEmpty then
    defaultOrigins.insert currentBlock |>.insert authorizerBlockId
  else
    let start := Origin.empty.insert authorizerBlockId |>.insert currentBlock
    scopes.foldl (fun acc scope =>
      match scope with
      | .authority => acc.insert 0
      | .previous =>
        if currentBlock != authorizerBlockId then
          (List.range (currentBlock + 1)).foldl (fun acc i => acc.insert i) acc
        else acc
      | .publicKey keyId =>
        match publicKeyToBlockId.find? (fun (k, _) => k == keyId) with
        | some (_, ids) => ids.foldl (fun acc i => acc.insert i) acc
        | none => acc) start

/-- May a fact with this origin be used? -/
def contains (t : TrustedOrigins) (factOrigin : Origin) : Bool := t.isSuperset factOrigin

end TrustedOrigins

namespace Predicate

/-- Ordering on predicates: by name, then by arguments. -/
def compare (a b : Predicate) : Ordering :=
  match Ord.compare a.name b.name with
  | .eq => Term.compareList a.terms b.terms
  | o => o

end Predicate

namespace Fact

/-- Ordering on facts, inherited from predicates. -/
def compare (a b : Fact) : Ordering := Predicate.compare a.predicate b.predicate

/-- Structural equality. -/
def beq (a b : Fact) : Bool := compare a b == .eq

end Fact

/-- Insert into a sorted, deduplicated list of facts. -/
def factInsert (f : Fact) : List Fact → List Fact
  | [] => [f]
  | x :: xs =>
    match Fact.compare f x with
    | .lt => f :: x :: xs
    | .eq => x :: xs
    | .gt => x :: factInsert f xs

/-- Facts grouped by origin.  Groups are kept in ascending origin order and each
group's facts are sorted, so that a world has one canonical form. -/
abbrev FactSet := List (Origin × List Fact)

namespace FactSet

/-- The empty set. -/
def empty : FactSet := []

/-- Add a fact under an origin. -/
def insert (s : FactSet) (origin : Origin) (f : Fact) : FactSet :=
  match s with
  | [] => [(origin, [f])]
  | (o, facts) :: rest =>
    match Origin.compare origin o with
    | .lt => (origin, [f]) :: (o, facts) :: rest
    | .eq => (o, factInsert f facts) :: rest
    | .gt => (o, facts) :: insert rest origin f

/-- The total number of facts. -/
def size (s : FactSet) : Nat := s.foldl (fun acc (_, facts) => acc + facts.length) 0

/-- Merge another set in. -/
def merge (s other : FactSet) : FactSet :=
  other.foldl (fun acc (o, facts) => facts.foldl (fun acc f => acc.insert o f) acc) s

/-- Every fact, paired with its origin. -/
def toList (s : FactSet) : List (Origin × Fact) :=
  s.flatMap fun (o, facts) => facts.map fun f => (o, f)

/-- The facts a rule with these trusted origins may use. -/
def iterator (s : FactSet) (trusted : TrustedOrigins) : List (Origin × Fact) :=
  (s.filter fun (o, _) => trusted.contains o).flatMap fun (o, facts) => facts.map fun f => (o, f)

end FactSet

/-- Rules grouped by the origins they trust; each rule remembers the block that
defined it. -/
abbrev RuleSet := List (TrustedOrigins × List (Nat × Rule))

namespace RuleSet

/-- The empty set. -/
def empty : RuleSet := []

/-- Add a rule under its trusted origins, preserving insertion order. -/
def insert (s : RuleSet) (origin : Nat) (trusted : TrustedOrigins) (r : Rule) : RuleSet :=
  if s.any (fun (t, _) => Origin.compare t trusted == .eq) then
    s.map fun (t, rules) =>
      if Origin.compare t trusted == .eq then (t, rules ++ [(origin, r)]) else (t, rules)
  else s ++ [(trusted, [(origin, r)])]

end RuleSet

/-- Partial bindings of the variables a rule's body mentions. -/
abbrev MatchedVariables := List (Nat × Option Term)

namespace MatchedVariables

/-- Start with every variable unbound. -/
def ofVariables (vars : List Nat) : MatchedVariables := vars.map fun v => (v, none)

/-- Bind a variable, failing if it is already bound to a different term. -/
def insert (m : MatchedVariables) (k : Nat) (t : Term) : Option MatchedVariables :=
  match List.find? (fun (k', _) => k' == k) m with
  | none => none
  | some (_, none) => some (m.map fun (k', v) => if k' == k then (k', some t) else (k', v))
  | some (_, some v) => if Term.beq v t then some m else none

/-- The bindings, if every variable is bound. -/
def complete (m : MatchedVariables) : Option Bindings :=
  m.foldl (fun acc (k, v) => do
    let acc ← acc
    let v ← v
    pure (acc ++ [(k, v)])) (some [])

end MatchedVariables

/-- Can a fact's predicate match a rule's predicate?  Variables in the rule
match anything; a fact must not itself contain variables. -/
def matchPredicates (rulePred factPred : Predicate) : Bool :=
  rulePred.name == factPred.name &&
  rulePred.terms.length == factPred.terms.length &&
  (rulePred.terms.zip factPred.terms).all fun (r, f) =>
    match f, r with
    | .variable _, _ => false
    | _, .variable _ => true
    | _, _ => Term.beq r f

/-- All ways of matching `predicates` against `facts`, together with the origin
of the facts used.

This is the heart of rule application: it enumerates the combinations the rule
body admits, in the order the reference implementation produces them, which
determines which expression error is reported first. -/
def combine (vars : MatchedVariables) (predicates : List Predicate)
    (facts : List (Origin × Fact)) : List (Origin × Bindings) :=
  match predicates with
  | [] =>
    match vars.complete with
    | some b => [(Origin.empty, b)]
    | none => []
  | p :: rest =>
    facts.flatMap fun (origin, fact) =>
      if !matchPredicates p fact.predicate then []
      else
        match (p.terms.zip fact.predicate.terms).foldl (fun acc (key, value) =>
            match acc, key with
            | none, _ => none
            | some vars, .variable k => vars.insert k value
            | some vars, _ => some vars) (some vars) with
        | none => []
        | some vars =>
          if rest.isEmpty then
            match vars.complete with
            | some b => [(origin, b)]
            | none => []
          else (combine vars rest facts).map fun (o, b) => (o.union origin, b)

/-- Evaluate a rule's expressions against one candidate binding.

Returns whether the candidate survives; a non-boolean result is a type error, as
the specification requires expressions to evaluate to booleans. -/
def checkExpressions (externs : Externs) (symbols : SymbolTable) (expressions : List Expression)
    (values : Bindings) : Except ExpressionError Bool :=
  let rec go (es : List Expression) (table : TempSymbolTable) : Except ExpressionError Bool :=
    match es with
    | [] => pure true
    | e :: rest =>
      match evalExpression externs e values table with
      | (.error err, _) => throw err
      | (.ok (.bool true), table) => go rest table
      | (.ok (.bool false), _) => pure false
      | (.ok _, _) => throw .invalidType
  go expressions (TempSymbolTable.ofBase symbols)

/-- Instantiate a rule's head with a binding, if every head variable is bound. -/
def instantiateHead (head : Predicate) (values : Bindings) : Option Predicate := do
  let terms ← head.terms.mapM fun t =>
    match t with
    | .variable i => values.lookup? i
    | t => some t
  pure { head with terms }

/-- Apply a rule to the facts it trusts, producing every fact it derives. -/
def applyRule (externs : Externs) (symbols : SymbolTable) (r : Rule) (ruleOrigin : Nat)
    (facts : List (Origin × Fact)) : Except ExpressionError (List (Origin × Fact)) := do
  let candidates := combine (MatchedVariables.ofVariables r.bodyVariables) r.body facts
  let mut out : List (Origin × Fact) := []
  for (origin, values) in candidates do
    if ← checkExpressions externs symbols r.expressions values then
      match instantiateHead r.head values with
      | none => pure ()
      | some p => out := out ++ [(origin.insert ruleOrigin, ⟨p⟩)]
  pure out

/-- Does the rule match at least one combination of facts?

Stops at the first success, so an expression error is only reported if it is
reached before a successful match — the behaviour the reference implementation's
lazy iterator has. -/
def findMatch (externs : Externs) (symbols : SymbolTable) (r : Rule)
    (facts : List (Origin × Fact)) : Except ExpressionError Bool := do
  let candidates := combine (MatchedVariables.ofVariables r.bodyVariables) r.body facts
  let rec go (cs : List (Origin × Bindings)) : Except ExpressionError Bool := do
    match cs with
    | [] => pure false
    | (_, values) :: rest =>
      if ← checkExpressions externs symbols r.expressions values then
        match instantiateHead r.head values with
        | none => go rest
        | some _ => pure true
      else go rest
  go candidates

/-- Do all matching combinations satisfy the rule's expressions, and is there at
least one?  This is the semantics of `check all`. -/
def checkMatchAll (externs : Externs) (symbols : SymbolTable) (r : Rule)
    (facts : List (Origin × Fact)) : Except ExpressionError Bool := do
  let candidates := combine (MatchedVariables.ofVariables r.bodyVariables) r.body facts
  let rec go (cs : List (Origin × Bindings)) (found : Bool) : Except ExpressionError Bool := do
    match cs with
    | [] => pure found
    | (_, values) :: rest =>
      if ← checkExpressions externs symbols r.expressions values then go rest true
      else pure false
  go candidates false

/-- The runtime limits of the datalog engine.

The reference implementation also bounds wall clock time; that bound is not
modelled here, since it would make the result of an authorization depend on the
speed of the machine rather than on the token. -/
structure RunLimits where
  /-- The largest number of facts a world may hold. -/
  maxFacts : Nat := 1000
  /-- The largest number of rule application rounds. -/
  maxIterations : Nat := 100
  deriving Repr, Inhabited

/-- A datalog world: the facts known so far and the rules that extend them. -/
structure World where
  /-- The facts, grouped by origin. -/
  facts : FactSet := FactSet.empty
  /-- The rules, grouped by the origins they trust. -/
  rules : RuleSet := RuleSet.empty
  /-- How many rounds of rule application have run. -/
  iterations : Nat := 0
  deriving Repr, Inhabited

namespace World

/-- Add a fact with a given origin. -/
def addFact (w : World) (origin : Origin) (f : Fact) : World :=
  { w with facts := w.facts.insert origin f }

/-- Add a rule with its trusted origins. -/
def addRule (w : World) (origin : Nat) (trusted : TrustedOrigins) (r : Rule) : World :=
  { w with rules := w.rules.insert origin trusted r }

/-- One round of rule application: apply every rule to the facts it trusts. -/
def step (externs : Externs) (symbols : SymbolTable) (w : World) :
    Except ExecutionError FactSet := do
  let mut newFacts := FactSet.empty
  for (trusted, rules) in w.rules do
    let visible := w.facts.iterator trusted
    for (origin, rule) in rules do
      match applyRule externs symbols rule origin visible with
      | .error e => throw (.expression e)
      | .ok derived =>
        for (o, f) in derived do
          newFacts := newFacts.insert o f
  pure newFacts

/-- Run the engine to a fixpoint, or until a limit is reached. -/
def run (externs : Externs) (symbols : SymbolTable) (limits : RunLimits) (w : World) :
    Except ExecutionError World := do
  let rec go (w : World) (index : Nat) (fuel : Nat) : Except ExecutionError World := do
    match fuel with
    | 0 => throw (.runLimit .tooManyIterations)
    | fuel + 1 =>
      let newFacts ← step externs symbols w
      let before := w.facts.size
      let w := { w with facts := w.facts.merge newFacts }
      if w.facts.size == before then
        pure { w with iterations := w.iterations + index }
      else
        let index := index + 1
        if index == limits.maxIterations then throw (.runLimit .tooManyIterations)
        else if w.facts.size ≥ limits.maxFacts then throw (.runLimit .tooManyFacts)
        else go w index fuel
  go w 0 (limits.maxIterations + 1)

/-- Does a query match, given the origins it trusts? -/
def queryMatch (externs : Externs) (symbols : SymbolTable) (w : World) (r : Rule)
    (trusted : TrustedOrigins) : Except ExecutionError Bool :=
  match findMatch externs symbols r (w.facts.iterator trusted) with
  | .error e => throw (.expression e)
  | .ok b => pure b

/-- Do all matches of a query satisfy it, given the origins it trusts? -/
def queryMatchAll (externs : Externs) (symbols : SymbolTable) (w : World) (r : Rule)
    (trusted : TrustedOrigins) : Except ExecutionError Bool :=
  match checkMatchAll externs symbols r (w.facts.iterator trusted) with
  | .error e => throw (.expression e)
  | .ok b => pure b

/-- The facts a query derives, which is how an authorizer answers questions
about a token. -/
def queryRule (externs : Externs) (symbols : SymbolTable) (w : World) (r : Rule)
    (ruleOrigin : Nat) (trusted : TrustedOrigins) : Except ExecutionError FactSet :=
  match applyRule externs symbols r ruleOrigin (w.facts.iterator trusted) with
  | .error e => throw (.expression e)
  | .ok derived => pure (derived.foldl (fun acc (o, f) => acc.insert o f) FactSet.empty)

end World

end Datalog
end LeanBiscuit
