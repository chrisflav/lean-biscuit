import LeanBiscuit.Datalog.Symbols
import LeanBiscuit.Util.Time

/-!
# Rendering datalog as source text

The printed form of facts, rules and checks is part of the observable behaviour
of an implementation: failed checks are reported by rendering the check that
failed.  This module reproduces the reference rendering exactly, including the
`&&!` / `||!` spelling that distinguishes the eager boolean operators from the
short-circuiting ones.
-/

namespace LeanBiscuit
namespace Datalog

mutual

/-- Render a term. -/
def printTerm (t : SymbolTable) : Term → String
  | .variable i => s!"${t.printSymbol i}"
  | .integer i => toString i
  | .str i => "\"" ++ t.printSymbol i ++ "\""
  | .date d =>
    -- the reference implementation reinterprets the stored `u64` as an `i64`
    let signed : Int := if d ≥ 2 ^ 63 then (d : Int) - 2 ^ 64 else (d : Int)
    match Time.formatRfc3339 signed with
    | some s => s
    | none => "<invalid date>"
  | .bytes b => s!"hex:{Bytes.toHex b}"
  | .bool b => if b then "true" else "false"
  | .set s =>
    if s.isEmpty then "{,}"
    else "{" ++ String.intercalate ", " (printTermList t s) ++ "}"
  | .null => "null"
  | .array a => "[" ++ String.intercalate ", " (printTermList t a) ++ "]"
  | .map m => "{" ++ String.intercalate ", " (printEntryList t m) ++ "}"

/-- Render each term of a list. -/
def printTermList (t : SymbolTable) : List Term → List String
  | [] => []
  | x :: xs => printTerm t x :: printTermList t xs

/-- Render each entry of a map. -/
def printEntryList (t : SymbolTable) : List (MapKey × Term) → List String
  | [] => []
  | (k, v) :: xs =>
    (match k with
     | .integer i => s!"{i}: {printTerm t v}"
     | .str s => "\"" ++ t.printSymbol s ++ "\": " ++ printTerm t v) :: printEntryList t xs

end

/-- Render a predicate. -/
def printPredicate (t : SymbolTable) (p : Predicate) : String :=
  let name := match t.get? p.name with | some n => n | none => "<?>"
  name ++ "(" ++ String.intercalate ", " (p.terms.map (printTerm t)) ++ ")"

/-- Render a fact. -/
def printFact (t : SymbolTable) (f : Fact) : String := printPredicate t f.predicate

/-- Render a unary operation applied to an already rendered operand. -/
def printUnary (t : SymbolTable) : Unary → String → String
  | .negate, v => s!"!{v}"
  | .parens, v => s!"({v})"
  | .length, v => s!"{v}.length()"
  | .typeOf, v => s!"{v}.type()"
  | .ffi name, v => s!"{v}.extern::{t.printSymbol name}()"

/-- Render a binary operation applied to two already rendered operands. -/
def printBinary (t : SymbolTable) : Binary → String → String → String
  | .lessThan, l, r => s!"{l} < {r}"
  | .greaterThan, l, r => s!"{l} > {r}"
  | .lessOrEqual, l, r => s!"{l} <= {r}"
  | .greaterOrEqual, l, r => s!"{l} >= {r}"
  | .equal, l, r => s!"{l} === {r}"
  | .heterogeneousEqual, l, r => s!"{l} == {r}"
  | .notEqual, l, r => s!"{l} !== {r}"
  | .heterogeneousNotEqual, l, r => s!"{l} != {r}"
  | .contains, l, r => s!"{l}.contains({r})"
  | .startsWith, l, r => s!"{l}.starts_with({r})"
  | .endsWith, l, r => s!"{l}.ends_with({r})"
  | .regex, l, r => s!"{l}.matches({r})"
  | .add, l, r => s!"{l} + {r}"
  | .sub, l, r => s!"{l} - {r}"
  | .mul, l, r => s!"{l} * {r}"
  | .div, l, r => s!"{l} / {r}"
  | .and, l, r => s!"{l} &&! {r}"
  | .or, l, r => s!"{l} ||! {r}"
  | .intersection, l, r => s!"{l}.intersection({r})"
  | .union, l, r => s!"{l}.union({r})"
  | .bitwiseAnd, l, r => s!"{l} & {r}"
  | .bitwiseOr, l, r => s!"{l} | {r}"
  | .bitwiseXor, l, r => s!"{l} ^ {r}"
  | .lazyAnd, l, r => s!"{l} && {r}"
  | .lazyOr, l, r => s!"{l} || {r}"
  | .all, l, r => s!"{l}.all({r})"
  | .any, l, r => s!"{l}.any({r})"
  | .get, l, r => s!"{l}.get({r})"
  | .ffi name, l, r => s!"{l}.extern::{t.printSymbol name}({r})"
  | .tryOr, l, r => s!"{l}.try_or({r})"

mutual

/-- Render an opcode sequence by running the stack machine over strings.
Returns `none` if the sequence is not well formed. -/
def printOps (t : SymbolTable) (ops : List Op) : Option String :=
  match printOpsOnto t ops [] with
  | some [s] => some s
  | _ => none

/-- Run the printing stack machine, starting from `stack`. -/
def printOpsOnto (t : SymbolTable) : List Op → List String → Option (List String)
  | [], stack => some stack
  | .value v :: rest, stack => printOpsOnto t rest (printTerm t v :: stack)
  | .unary u :: rest, stack =>
    match stack with
    | x :: stack => printOpsOnto t rest (printUnary t u x :: stack)
    | _ => none
  | .binary b :: rest, stack =>
    match stack with
    | r :: l :: stack => printOpsOnto t rest (printBinary t b l r :: stack)
    | _ => none
  | .closure params body :: rest, stack =>
    match printOps t body with
    | none => none
    | some bodyStr =>
      let s :=
        if params.isEmpty then bodyStr
        else String.intercalate ", " (params.map fun p => printTerm t (.variable p))
               ++ " -> " ++ bodyStr
      printOpsOnto t rest (s :: stack)

end

/-- Render an expression, or a diagnostic if it is malformed. -/
def printExpression (t : SymbolTable) (e : Expression) : String :=
  match printOps t e.ops with
  | some s => s
  | none => s!"<invalid expression: {reprStr e.ops}>"

/-- Render a trust annotation. -/
def printScope (t : SymbolTable) : Scope → String
  | .authority => "authority"
  | .previous => "previous"
  | .publicKey i =>
    match t.getKey? i with
    | some k => k.print
    | none => "<unknown public key id>"

/-- Render the body of a rule: predicates, then expressions, then the trust
annotation. -/
def printRuleBody (t : SymbolTable) (r : Rule) : String :=
  let preds := r.body.map (printPredicate t)
  let exprs := r.expressions.map (printExpression t)
  let e :=
    if exprs.isEmpty then ""
    else if preds.isEmpty then String.intercalate ", " exprs
    else ", " ++ String.intercalate ", " exprs
  let scopes :=
    if r.scopes.isEmpty then ""
    else " trusting " ++ String.intercalate ", " (r.scopes.map (printScope t))
  String.intercalate ", " preds ++ e ++ scopes

/-- Render a rule. -/
def printRule (t : SymbolTable) (r : Rule) : String :=
  printPredicate t r.head ++ " <- " ++ printRuleBody t r

/-- Render a check. -/
def printCheck (t : SymbolTable) (c : Check) : String :=
  let kind := match c.kind with
    | .one => "check if"
    | .all => "check all"
    | .reject => "reject if"
  kind ++ " " ++ String.intercalate " or " (c.queries.map (printRuleBody t))

/-- Render a policy. -/
def printPolicy (t : SymbolTable) (p : Policy) : String :=
  let kind := match p.kind with
    | .allow => "allow"
    | .deny => "deny"
  if p.queries.isEmpty then kind
  else kind ++ " if " ++ String.intercalate " or " (p.queries.map (printRuleBody t))

end Datalog
end LeanBiscuit
