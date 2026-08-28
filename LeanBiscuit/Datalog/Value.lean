import LeanBiscuit.Datalog.Symbols

/-!
# Resolved values

Terms carry interned string indices, which are meaningless outside the token
that defines them.  Host-provided external functions work with resolved values
instead, so that a caller never has to know about the symbol table.
-/

namespace LeanBiscuit
namespace Datalog

/-- A map key with its string resolved. -/
inductive ValueKey where
  /-- An integer key. -/
  | integer (value : Int)
  /-- A string key. -/
  | str (value : String)
  deriving Repr, DecidableEq, Inhabited

/-- A term with all interned strings resolved. -/
inductive Value where
  /-- A signed 64 bit integer. -/
  | integer (value : Int)
  /-- A string. -/
  | str (value : String)
  /-- A date, in seconds since the Unix epoch. -/
  | date (value : Nat)
  /-- A byte string. -/
  | bytes (value : Bytes)
  /-- A boolean. -/
  | bool (value : Bool)
  /-- A set. -/
  | set (elements : List Value)
  /-- The absence of a value. -/
  | null
  /-- An array. -/
  | array (elements : List Value)
  /-- A map. -/
  | map (entries : List (ValueKey × Value))
  deriving Repr, Inhabited

namespace Value

mutual

/-- Resolve a term against a symbol table. -/
def ofTerm (t : TempSymbolTable) : Term → Except ExpressionError Value
  | .variable _ => throw .invalidType
  | .integer i => pure (.integer i)
  | .str i => match t.get? i with
    | some s => pure (.str s)
    | none => throw (.unknownSymbol i)
  | .date d => pure (.date d)
  | .bytes b => pure (.bytes b)
  | .bool b => pure (.bool b)
  | .set l => do pure (.set (← ofTermList t l))
  | .null => pure .null
  | .array l => do pure (.array (← ofTermList t l))
  | .map entries => do pure (.map (← ofEntryList t entries))

/-- Resolve each term of a list. -/
def ofTermList (t : TempSymbolTable) : List Term → Except ExpressionError (List Value)
  | [] => pure []
  | x :: xs => do pure ((← ofTerm t x) :: (← ofTermList t xs))

/-- Resolve each entry of a map. -/
def ofEntryList (t : TempSymbolTable) :
    List (MapKey × Term) → Except ExpressionError (List (ValueKey × Value))
  | [] => pure []
  | (k, v) :: xs => do
    let k ← match k with
      | .integer i => pure (ValueKey.integer i)
      | .str i => match t.get? i with
        | some s => pure (ValueKey.str s)
        | none => throw (.unknownSymbol i)
    pure ((k, ← ofTerm t v) :: (← ofEntryList t xs))

end

mutual

/-- Intern a value's strings, producing a term. -/
def toTerm (t : TempSymbolTable) : Value → Term × TempSymbolTable
  | .integer i => (.integer i, t)
  | .str s => let (i, t) := t.insert s; (.str i, t)
  | .date d => (.date d, t)
  | .bytes b => (.bytes b, t)
  | .bool b => (.bool b, t)
  | .null => (.null, t)
  | .set l => let (terms, t) := toTermList t l; (.set (mkSet terms), t)
  | .array l => let (terms, t) := toTermList t l; (.array terms, t)
  | .map entries => let (es, t) := toEntryList t entries; (.map (mkMap es), t)

/-- Intern each value of a list. -/
def toTermList (t : TempSymbolTable) : List Value → List Term × TempSymbolTable
  | [] => ([], t)
  | x :: xs =>
    let (x, t) := toTerm t x
    let (xs, t) := toTermList t xs
    (x :: xs, t)

/-- Intern each entry of a map. -/
def toEntryList (t : TempSymbolTable) :
    List (ValueKey × Value) → List (MapKey × Term) × TempSymbolTable
  | [] => ([], t)
  | (k, v) :: xs =>
    let (k, t) := match k with
      | .integer i => (MapKey.integer i, t)
      | .str s => let (i, t) := t.insert s; (MapKey.str i, t)
    let (v, t) := toTerm t v
    let (xs, t) := toEntryList t xs
    ((k, v) :: xs, t)

end

end Value

/-- A function provided by the host language, callable from datalog through
`extern::name(…)`.  It receives the left operand and, for the binary form, the
right one, and either returns a value or an error message. -/
abbrev ExternFunc := Value → Option Value → Except String Value

/-- The set of external functions available to an authorizer. -/
abbrev Externs := List (String × ExternFunc)

end Datalog
end LeanBiscuit
