import LeanBiscuit.Datalog.Ast
import LeanBiscuit.Crypto.PublicKey

/-!
# Symbol and public key tables

To keep tokens small, strings and public keys are interned: predicates and terms
refer to them by index.  Indices below `offset` are reserved for a fixed default
table that every implementation knows, so common names such as `read` or
`resource` cost nothing to transmit.

Blocks contribute their own symbols, and it is an error for two blocks to
declare the same one, since that would make the table ambiguous.
-/

namespace LeanBiscuit
namespace Datalog

/-- The default symbols, shared by every implementation. -/
def defaultSymbols : Array String := #[
  "read", "write", "resource", "operation", "right", "time", "role", "owner",
  "tenant", "namespace", "user", "team", "service", "admin", "email", "group",
  "member", "ip_address", "client", "client_ip", "domain", "path", "version",
  "cluster", "node", "hostname", "nonce", "query"]

/-- Indices below this are reserved for `defaultSymbols`. -/
def symbolOffset : Nat := 1024

/-- The interning tables for a token or an authorizer. -/
structure SymbolTable where
  /-- Symbols beyond the default table; entry `i` has index `symbolOffset + i`. -/
  symbols : Array String := #[]
  /-- Public keys referenced by scope annotations. -/
  publicKeys : Array PublicKey := #[]
  deriving Repr, Inhabited

namespace SymbolTable

/-- The empty table.  Note that the default symbols are always available; they
are not stored. -/
def empty : SymbolTable := {}

/-- Look up the string for an index. -/
def get? (t : SymbolTable) (i : Nat) : Option String :=
  if i ≥ symbolOffset then t.symbols[i - symbolOffset]?
  else defaultSymbols[i]?

/-- Print a symbol, falling back to `<i?>` for unknown indices as the reference
implementation does when rendering a partially known table. -/
def printSymbol (t : SymbolTable) (i : Nat) : String :=
  match t.get? i with
  | some s => s
  | none => s!"<{i}?>"

/-- The index of a string, if it is already interned. -/
def find? (t : SymbolTable) (s : String) : Option Nat :=
  match defaultSymbols.findIdx? (· == s) with
  | some i => some i
  | none => (t.symbols.findIdx? (· == s)).map (· + symbolOffset)

/-- Intern a string, returning its index and the possibly extended table. -/
def insert (t : SymbolTable) (s : String) : Nat × SymbolTable :=
  match t.find? s with
  | some i => (i, t)
  | none => (t.symbols.size + symbolOffset, { t with symbols := t.symbols.push s })

/-- Intern a string, discarding the index. -/
def add (t : SymbolTable) (s : String) : SymbolTable := (t.insert s).2

/-- Do the two tables share no symbol? -/
def isDisjoint (a b : SymbolTable) : Bool :=
  b.symbols.all fun s => !a.symbols.contains s

/-- Build a table from a block's symbol list, rejecting any symbol that shadows
a default one. -/
def ofStrings (l : List String) : Except FormatError SymbolTable :=
  if l.any (fun s => defaultSymbols.contains s) then throw .symbolTableOverlap
  else pure { symbols := l.toArray }

/-- Append another table's symbols, rejecting duplicates. -/
def extendSymbols (t other : SymbolTable) : Except FormatError SymbolTable :=
  if !t.isDisjoint other then throw .symbolTableOverlap
  else pure { t with symbols := t.symbols ++ other.symbols }

/-- The public key at an index of the key table. -/
def getKey? (t : SymbolTable) (i : Nat) : Option PublicKey := t.publicKeys[i]?

/-- Intern a public key, returning its index. -/
def insertKey (t : SymbolTable) (k : PublicKey) : Nat × SymbolTable :=
  match t.publicKeys.findIdx? (· == k) with
  | some i => (i, t)
  | none => (t.publicKeys.size, { t with publicKeys := t.publicKeys.push k })

/-- Intern a public key, rejecting one that is already present.  Blocks must not
redeclare a key that an earlier block already contributed. -/
def insertKeyFallible (t : SymbolTable) (k : PublicKey) :
    Except FormatError (Nat × SymbolTable) :=
  if t.publicKeys.contains k then throw .publicKeyTableOverlap
  else pure (t.publicKeys.size, { t with publicKeys := t.publicKeys.push k })

end SymbolTable

/-- A symbol table extended with symbols created during expression evaluation,
such as the result of a string concatenation.  These symbols are local to one
evaluation and never reach the token. -/
structure TempSymbolTable where
  /-- The table this one extends. -/
  base : SymbolTable
  /-- The index the first temporary symbol gets. -/
  offset : Nat
  /-- The temporary symbols. -/
  extra : Array String := #[]
  deriving Repr, Inhabited

namespace TempSymbolTable

/-- Start a temporary table on top of `base`. -/
def ofBase (base : SymbolTable) : TempSymbolTable :=
  { base, offset := symbolOffset + base.symbols.size }

/-- Look up the string for an index. -/
def get? (t : TempSymbolTable) (i : Nat) : Option String :=
  if i ≥ t.offset then t.extra[i - t.offset]? else t.base.get? i

/-- Intern a string in the temporary table. -/
def insert (t : TempSymbolTable) (s : String) : Nat × TempSymbolTable :=
  match t.base.find? s with
  | some i => (i, t)
  | none =>
    match t.extra.findIdx? (· == s) with
    | some i => (t.offset + i, t)
    | none => (t.offset + t.extra.size, { t with extra := t.extra.push s })

end TempSymbolTable

end Datalog
end LeanBiscuit
