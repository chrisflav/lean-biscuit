import LeanBiscuit.Datalog.Value
import LeanBiscuit.Datalog.Print
import LeanBiscuit.Util.Regex

/-!
# Expression evaluation

Expressions are evaluated by a stack machine.  Each opcode either pushes a value
(replacing variables by their bindings), pops one or two values and pushes a
result, or pushes a closure to be evaluated later.  A well formed expression
leaves exactly one value on the stack.

Evaluation can extend the symbol table — string concatenation and `type()`
produce strings that were not interned before — so it runs in a state monad over
a `TempSymbolTable`.  Those symbols are local to the evaluation and never become
part of the token.
-/

namespace LeanBiscuit
namespace Datalog

/-- Bindings of rule variables to the terms they matched. -/
abbrev Bindings := List (Nat × Term)

namespace Bindings

/-- The term bound to a variable, if any. -/
def lookup? (b : Bindings) (i : Nat) : Option Term :=
  (List.find? (fun (k, _) => k == i) b).map (·.2)

/-- Is the variable bound? -/
def has (b : Bindings) (i : Nat) : Bool := b.any (fun (k, _) => k == i)

/-- Bind a variable, replacing any existing binding. -/
def bind (b : Bindings) (i : Nat) (t : Term) : Bindings :=
  b.filter (fun (k, _) => k != i) ++ [(i, t)]

end Bindings

/-- The evaluation monad: failures are expression errors, and the state is the
temporary symbol table. -/
abbrev EvalM := ExceptT ExpressionError (StateM TempSymbolTable)

/-- Look up a symbol, failing if it is unknown. -/
def getSymbol (i : Nat) : EvalM String := do
  match (← get).get? i with
  | some s => pure s
  | none => throw (.unknownSymbol i)

/-- Intern a string in the temporary table. -/
def internSymbol (s : String) : EvalM Nat := do
  let (i, t) := (← get).insert s
  set t
  pure i

/-! ## Signed 64 bit arithmetic

The specification requires integer operations to be checked: an operation whose
result leaves the range of a signed 64 bit integer makes the expression fail. -/

namespace Int64

/-- Addition, failing on overflow. -/
def add (a b : Int) : Except ExpressionError Term :=
  let r := a + b
  if inInt64Range r then pure (.integer r) else throw .overflow

/-- Subtraction, failing on overflow. -/
def sub (a b : Int) : Except ExpressionError Term :=
  let r := a - b
  if inInt64Range r then pure (.integer r) else throw .overflow

/-- Multiplication, failing on overflow. -/
def mul (a b : Int) : Except ExpressionError Term :=
  let r := a * b
  if inInt64Range r then pure (.integer r) else throw .overflow

/-- Division, truncating towards zero.  A zero divisor fails, as does the one
quotient that does not fit. -/
def div (a b : Int) : Except ExpressionError Term :=
  if b == 0 then throw .divideByZero
  else
    let r := a.tdiv b
    if inInt64Range r then pure (.integer r) else throw .divideByZero

/-- The unsigned 64 bit representation of a signed value. -/
def toU64 (a : Int) : Nat := (if a < 0 then a + 2 ^ 64 else a).toNat

/-- The signed value of an unsigned 64 bit representation. -/
def ofU64 (a : Nat) : Int := if a ≥ 2 ^ 63 then (a : Int) - 2 ^ 64 else (a : Int)

/-- Bitwise conjunction of the two's complement representations. -/
def bitAnd (a b : Int) : Int := ofU64 (toU64 a &&& toU64 b)

/-- Bitwise disjunction of the two's complement representations. -/
def bitOr (a b : Int) : Int := ofU64 (toU64 a ||| toU64 b)

/-- Bitwise exclusive or of the two's complement representations. -/
def bitXor (a b : Int) : Int := ofU64 (toU64 a ^^^ toU64 b)

end Int64

/-- Does `needle` occur in `haystack`? -/
def isSubstring (needle haystack : String) : Bool :=
  let n := needle.toList
  let rec go (h : List Char) : Bool :=
    n.isPrefixOf h || match h with
      | [] => false
      | _ :: rest => go rest
  go haystack.toList

/-- The name of a term's type, as reported by `type()`. -/
def typeName : Term → Option String
  | .variable _ => none
  | .integer _ => some "integer"
  | .str _ => some "string"
  | .date _ => some "date"
  | .bytes _ => some "bytes"
  | .bool _ => some "bool"
  | .set _ => some "set"
  | .null => some "null"
  | .array _ => some "array"
  | .map _ => some "map"

/-- Call a host function, resolving the operands' strings first and interning
the strings of the result. -/
def callExtern (externs : Externs) (name : String) (left : Term) (right : Option Term) :
    EvalM Term := do
  match externs.find? (fun (n, _) => n == name) with
  | none => throw (.undefinedExtern name)
  | some (_, f) =>
    let table ← get
    let left ← liftM (Value.ofTerm table left)
    let right ← match right with
      | none => pure none
      | some r => do pure (some (← liftM (Value.ofTerm table r)))
    match f left right with
    | .error e => throw (.externEvalError name e)
    | .ok v =>
      let (t, table) := Value.toTerm (← get) v
      set table
      pure t

/-- Evaluate a unary opcode. -/
def evalUnary (externs : Externs) : Unary → Term → EvalM Term
  | .negate, .bool b => pure (.bool !b)
  | .parens, t => pure t
  | .length, .str i => do pure (.integer ((← getSymbol i).utf8ByteSize : Int))
  | .length, .bytes b => pure (.integer (b.size : Int))
  | .length, .set l => pure (.integer (l.length : Int))
  | .length, .array l => pure (.integer (l.length : Int))
  | .length, .map m => pure (.integer (m.length : Int))
  | .typeOf, t =>
    match typeName t with
    | none => throw .invalidType
    | some n => do pure (.str (← internSymbol n))
  | .ffi name, t => do callExtern externs (← getSymbol name) t none
  | _, _ => throw .invalidType

/-- Is this a strict or heterogeneous equality opcode? -/
def isEqualOp : Binary → Bool
  | .equal | .heterogeneousEqual => true
  | _ => false

/-- Is this a strict or heterogeneous inequality opcode? -/
def isNotEqualOp : Binary → Bool
  | .notEqual | .heterogeneousNotEqual => true
  | _ => false

/-- The operations that are available for any pair of same-typed operands:
equality, inequality, an external call, and the heterogeneous fallbacks. -/
def evalSameTypeFallback (externs : Externs) (op : Binary) (left right : Term)
    (eq : Bool) (allowHeterogeneous : Bool) : EvalM Term := do
  if isEqualOp op then pure (.bool eq)
  else if isNotEqualOp op then pure (.bool !eq)
  else match op with
    | .ffi name => do callExtern externs (← getSymbol name) left right
    | .heterogeneousEqual => if allowHeterogeneous then pure (.bool false) else throw .invalidType
    | .heterogeneousNotEqual => if allowHeterogeneous then pure (.bool true) else throw .invalidType
    | _ => throw .invalidType

/-- Is `t` a key of the map `m`? -/
def mapHasKey (m : List (MapKey × Term)) (t : Term) : Bool :=
  m.any fun (k, _) =>
    match k, t with
    | .integer i, .integer j => i == j
    | .str i, .str j => i == j
    | _, _ => false

/-- Evaluate a binary opcode whose operands are both values.

The order of the cases follows the reference implementation, which is
observable: the `null` cases are tried before the array and map cases, and the
heterogeneous fallbacks come last. -/
def evalBinary (externs : Externs) (op : Binary) (left right : Term) : EvalM Term := do
  match op, left, right with
  -- integers
  | .lessThan, .integer a, .integer b => pure (.bool (a < b))
  | .greaterThan, .integer a, .integer b => pure (.bool (a > b))
  | .lessOrEqual, .integer a, .integer b => pure (.bool (a ≤ b))
  | .greaterOrEqual, .integer a, .integer b => pure (.bool (a ≥ b))
  | .add, .integer a, .integer b => liftM (Int64.add a b)
  | .sub, .integer a, .integer b => liftM (Int64.sub a b)
  | .mul, .integer a, .integer b => liftM (Int64.mul a b)
  | .div, .integer a, .integer b => liftM (Int64.div a b)
  | .bitwiseAnd, .integer a, .integer b => pure (.integer (Int64.bitAnd a b))
  | .bitwiseOr, .integer a, .integer b => pure (.integer (Int64.bitOr a b))
  | .bitwiseXor, .integer a, .integer b => pure (.integer (Int64.bitXor a b))
  | op, .integer a, .integer b => evalSameTypeFallback externs op left right (a == b) true
  -- strings
  | .startsWith, .str a, .str b => do
    pure (.bool ((← getSymbol a).startsWith (← getSymbol b)))
  | .endsWith, .str a, .str b => do
    pure (.bool ((← getSymbol a).endsWith (← getSymbol b)))
  | .regex, .str a, .str b => do
    pure (.bool (Regex.isMatch (← getSymbol b) (← getSymbol a)))
  | .contains, .str a, .str b => do
    pure (.bool (isSubstring (← getSymbol b) (← getSymbol a)))
  | .add, .str a, .str b => do
    let s := (← getSymbol a) ++ (← getSymbol b)
    pure (.str (← internSymbol s))
  | op, .str a, .str b => evalSameTypeFallback externs op left right (a == b) true
  -- dates
  | .lessThan, .date a, .date b => pure (.bool (a < b))
  | .greaterThan, .date a, .date b => pure (.bool (a > b))
  | .lessOrEqual, .date a, .date b => pure (.bool (a ≤ b))
  | .greaterOrEqual, .date a, .date b => pure (.bool (a ≥ b))
  | op, .date a, .date b => evalSameTypeFallback externs op left right (a == b) true
  -- byte strings
  | op, .bytes a, .bytes b =>
    evalSameTypeFallback externs op left right (Bytes.compare a b == .eq) true
  -- sets
  | .intersection, .set a, .set b => pure (.set (setIntersection a b))
  | .union, .set a, .set b => pure (.set (setUnion a b))
  | .contains, .set a, .set b => pure (.bool (setIsSuperset a b))
  | op, .set a, .set b =>
    evalSameTypeFallback externs op left right (Term.compareList a b == .eq) false
  | .contains, .set a, .integer _ => pure (.bool (setContains a right))
  | .contains, .set a, .date _ => pure (.bool (setContains a right))
  | .contains, .set a, .bool _ => pure (.bool (setContains a right))
  | .contains, .set a, .str _ => pure (.bool (setContains a right))
  | .contains, .set a, .bytes _ => pure (.bool (setContains a right))
  -- booleans
  | .and, .bool a, .bool b => pure (.bool (a && b))
  | .or, .bool a, .bool b => pure (.bool (a || b))
  | op, .bool a, .bool b => evalSameTypeFallback externs op left right (a == b) true
  -- null
  | op, .null, .null => evalSameTypeFallback externs op left right true false
  | .heterogeneousEqual, .null, _ => pure (.bool false)
  | .heterogeneousEqual, _, .null => pure (.bool false)
  | .heterogeneousNotEqual, .null, _ => pure (.bool true)
  | .heterogeneousNotEqual, _, .null => pure (.bool true)
  -- arrays
  | .startsWith, .array a, .array b => pure (.bool (Term.compareList (a.take b.length) b == .eq))
  | .endsWith, .array a, .array b =>
    pure (.bool (Term.compareList (a.drop (a.length - b.length)) b == .eq))
  | .get, .array a, .integer i =>
    if i < 0 then pure .null else pure (a[i.toNat]?.getD .null)
  | .contains, .array a, _ => pure (.bool (a.any (Term.beq right)))
  | op, .array a, .array b =>
    evalSameTypeFallback externs op left right (Term.compareList a b == .eq) false
  -- maps
  | .get, .map m, .integer i =>
    pure ((List.find? (fun (k, _) => MapKey.compare k (.integer i) == .eq) m).map (·.2)
      |>.getD .null)
  | .get, .map m, .str s =>
    pure ((List.find? (fun (k, _) => MapKey.compare k (.str s) == .eq) m).map (·.2) |>.getD .null)
  | .contains, .map m, _ => pure (.bool (mapHasKey m right))
  | op, .map a, .map b =>
    evalSameTypeFallback externs op left right (Term.compareEntries a b == .eq) false
  -- fallbacks
  | .heterogeneousEqual, _, _ => pure (.bool false)
  | .heterogeneousNotEqual, _, _ => pure (.bool true)
  | .ffi name, _, _ => do callExtern externs (← getSymbol name) left right
  | _, _, _ => throw .invalidType

/-- A value on the evaluation stack. -/
inductive StackElem where
  /-- An evaluated term. -/
  | term (value : Term)
  /-- An unevaluated closure. -/
  | closure (params : List Nat) (ops : List Op)
  deriving Repr, Inhabited

mutual

/-- The size of one opcode, counting a closure's body. -/
def opSize : Op → Nat
  | .closure _ body => 1 + opsSize body
  | _ => 1

/-- The total number of opcodes in a sequence, counting nested closures.  This
bounds how deeply closures can nest, and so bounds the evaluator's recursion. -/
def opsSize : List Op → Nat
  | [] => 0
  | o :: rest => opSize o + opsSize rest

end

/-- A map entry as seen by `any` and `all`: the two element array `[key, value]`. -/
def mapEntryAsArray (e : MapKey × Term) : Term :=
  .array [(match e.1 with | .integer i => .integer i | .str s => .str s), e.2]

mutual

/-- Evaluate an opcode sequence to the single value it must leave on the stack.

`fuel` bounds how deeply closures may nest; `evalExpression` derives a bound
from the expression itself, so a well formed expression never exhausts it. -/
def evalOps (externs : Externs) (fuel : Nat) (ops : List Op) (values : Bindings) : EvalM Term := do
  match ← evalStack externs fuel ops values [] with
  | [.term t] => pure t
  | _ => throw .invalidStack
termination_by (fuel, 3, ops.length)

/-- Run the stack machine over `ops`, with `stack` holding the topmost element
first. -/
def evalStack (externs : Externs) (fuel : Nat) (ops : List Op) (values : Bindings)
    (stack : List StackElem) : EvalM (List StackElem) := do
  match ops with
  | [] => pure stack
  | .value (.variable i) :: rest =>
    match values.lookup? i with
    | some t => evalStack externs fuel rest values (.term t :: stack)
    | none => throw (.unknownVariable i)
  | .value t :: rest => evalStack externs fuel rest values (.term t :: stack)
  | .closure params body :: rest =>
    evalStack externs fuel rest values (.closure params body :: stack)
  | .unary u :: rest =>
    match stack with
    | .term t :: stack => do
      let r ← evalUnary externs u t
      evalStack externs fuel rest values (.term r :: stack)
    | _ => throw .invalidStack
  | .binary op :: rest =>
    match stack with
    | .term r :: .term l :: stack => do
      let v ← evalBinary externs op l r
      evalStack externs fuel rest values (.term v :: stack)
    | .closure params body :: .term l :: stack => do
      if params.any values.has then throw .shadowedVariable
      let v ← evalClosure externs fuel op l body params values
      evalStack externs fuel rest values (.term v :: stack)
    | .term r :: .closure params body :: stack => do
      if params.any values.has then throw .shadowedVariable
      let v ← evalClosure externs fuel op r body params values
      evalStack externs fuel rest values (.term v :: stack)
    | _ => throw .invalidStack
termination_by (fuel, 2, ops.length)

/-- Evaluate a binary opcode one of whose operands is an unevaluated closure:
the lazy boolean operators, `try_or`, and the higher order `any` and `all`. -/
def evalClosure (externs : Externs) (fuel : Nat) (op : Binary) (left : Term) (body : List Op)
    (params : List Nat) (values : Bindings) : EvalM Term := do
  match fuel with
  | 0 => throw .invalidStack
  | fuel' + 1 =>
    match op, left, params with
    | .tryOr, fallback, [] =>
      tryCatch (evalOps externs fuel' body values) (fun _ => pure fallback)
    | .lazyOr, .bool true, [] => pure (.bool true)
    | .lazyOr, .bool false, [] => evalOps externs fuel' body values
    | .lazyAnd, .bool false, [] => pure (.bool false)
    | .lazyAnd, .bool true, [] => evalOps externs fuel' body values
    | .all, .set elements, [param] => evalAll externs fuel' body param values elements
    | .any, .set elements, [param] => evalAny externs fuel' body param values elements
    | .all, .array elements, [param] => evalAll externs fuel' body param values elements
    | .any, .array elements, [param] => evalAny externs fuel' body param values elements
    | .all, .map entries, [param] =>
      evalAll externs fuel' body param values (entries.map mapEntryAsArray)
    | .any, .map entries, [param] =>
      evalAny externs fuel' body param values (entries.map mapEntryAsArray)
    | _, _, _ => throw .invalidType
termination_by (fuel, 1, 0)

/-- Does the closure hold for every element? -/
def evalAll (externs : Externs) (fuel : Nat) (body : List Op) (param : Nat) (values : Bindings)
    (elements : List Term) : EvalM Term :=
  match fuel, elements with
  | _, [] => pure (.bool true)
  | 0, _ => throw .invalidStack
  | fuel' + 1, e :: rest => do
    match ← evalOps externs fuel' body (values.bind param e) with
    | .bool true => evalAll externs (fuel' + 1) body param values rest
    | .bool false => pure (.bool false)
    | _ => throw .invalidType
termination_by (fuel, 0, elements.length)

/-- Does the closure hold for some element? -/
def evalAny (externs : Externs) (fuel : Nat) (body : List Op) (param : Nat) (values : Bindings)
    (elements : List Term) : EvalM Term :=
  match fuel, elements with
  | _, [] => pure (.bool false)
  | 0, _ => throw .invalidStack
  | fuel' + 1, e :: rest => do
    match ← evalOps externs fuel' body (values.bind param e) with
    | .bool false => evalAny externs (fuel' + 1) body param values rest
    | .bool true => pure (.bool true)
    | _ => throw .invalidType
termination_by (fuel, 0, elements.length)

end

/-- Evaluate an expression against a set of bindings, threading the temporary
symbol table. -/
def evalExpression (externs : Externs) (e : Expression) (values : Bindings)
    (table : TempSymbolTable) : Except ExpressionError Term × TempSymbolTable :=
  (evalOps externs (2 * opsSize e.ops + 2) e.ops values).run.run table

end Datalog
end LeanBiscuit
