import LeanBiscuit.Datalog.Term

/-!
# Datalog syntax

Predicates, facts, rules, checks and policies, together with the opcode
representation of expressions.

Expressions are stored as a flat sequence of opcodes for a stack machine, which
is how they travel on the wire.  A `closure` opcode carries a nested sequence,
used for the lazy boolean operators and for the `any`/`all` higher order
operations.
-/

namespace LeanBiscuit
namespace Datalog

/-- A predicate: an interned name applied to a list of terms. -/
structure Predicate where
  /-- The interned predicate name. -/
  name : Nat
  /-- The arguments. -/
  terms : List Term
  deriving Repr, Inhabited

/-- A fact is a predicate without variables. -/
structure Fact where
  /-- The underlying predicate. -/
  predicate : Predicate
  deriving Repr, Inhabited

/-- A trust annotation, naming the blocks a rule may draw facts from. -/
inductive Scope where
  /-- Trust the authority block. -/
  | authority
  /-- Trust every preceding block.  Only meaningful inside a block. -/
  | previous
  /-- Trust blocks signed by the key at this index of the public key table. -/
  | publicKey (index : Nat)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Unary opcodes. -/
inductive Unary where
  /-- Boolean negation. -/
  | negate
  /-- Identity; recorded so that printing can reproduce the parentheses. -/
  | parens
  /-- Length of a string, byte string, set, array or map. -/
  | length
  /-- The name of a term's type, as a string. -/
  | typeOf
  /-- A call to a host-provided function. -/
  | ffi (name : Nat)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Binary opcodes. -/
inductive Binary where
  /-- `<` on integers and dates. -/
  | lessThan
  /-- `>` on integers and dates. -/
  | greaterThan
  /-- `<=` on integers and dates. -/
  | lessOrEqual
  /-- `>=` on integers and dates. -/
  | greaterOrEqual
  /-- `===`, which is a type error across different types. -/
  | equal
  /-- Membership, substring, or key lookup, depending on the operand types. -/
  | contains
  /-- `starts_with` on strings and arrays. -/
  | startsWith
  /-- `ends_with` on strings and arrays. -/
  | endsWith
  /-- `matches`: regular expression search. -/
  | regex
  /-- Integer addition, or string concatenation. -/
  | add
  /-- Integer subtraction. -/
  | sub
  /-- Integer multiplication. -/
  | mul
  /-- Integer division. -/
  | div
  /-- Eager boolean conjunction. -/
  | and
  /-- Eager boolean disjunction. -/
  | or
  /-- Set intersection. -/
  | intersection
  /-- Set union. -/
  | union
  /-- Bitwise and. -/
  | bitwiseAnd
  /-- Bitwise or. -/
  | bitwiseOr
  /-- Bitwise exclusive or. -/
  | bitwiseXor
  /-- `!==`. -/
  | notEqual
  /-- `==`, which is `false` across different types rather than an error. -/
  | heterogeneousEqual
  /-- `!=`. -/
  | heterogeneousNotEqual
  /-- Short-circuiting conjunction; the right operand is a closure. -/
  | lazyAnd
  /-- Short-circuiting disjunction; the right operand is a closure. -/
  | lazyOr
  /-- `all`: does every element satisfy the closure? -/
  | all
  /-- `any`: does some element satisfy the closure? -/
  | any
  /-- Indexing into an array or a map. -/
  | get
  /-- A call to a host-provided function. -/
  | ffi (name : Nat)
  /-- `try_or`: evaluate the left closure, falling back to the right value. -/
  | tryOr
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A stack machine opcode. -/
inductive Op where
  /-- Push a value.  A variable is replaced by its binding. -/
  | value (term : Term)
  /-- Pop one value, push the result. -/
  | unary (op : Unary)
  /-- Pop two values, push the result. -/
  | binary (op : Binary)
  /-- Push a closure, i.e. an unevaluated opcode sequence with parameters. -/
  | closure (params : List Nat) (ops : List Op)
  deriving Repr, Inhabited

/-- An expression is a sequence of opcodes that must leave exactly one boolean
on the stack. -/
structure Expression where
  /-- The opcodes, in evaluation order. -/
  ops : List Op
  deriving Repr, Inhabited

/-- A rule: a head derived from a body of predicates, filtered by expressions
and restricted to a set of trusted origins. -/
structure Rule where
  /-- The predicate produced when the body matches. -/
  head : Predicate
  /-- The predicates to match. -/
  body : List Predicate
  /-- Conditions every match must satisfy. -/
  expressions : List Expression
  /-- Trust annotations; empty means the default scope. -/
  scopes : List Scope
  deriving Repr, Inhabited

/-- The three flavours of check. -/
inductive CheckKind where
  /-- `check if`: at least one match must satisfy the expressions. -/
  | one
  /-- `check all`: every match must satisfy the expressions. -/
  | all
  /-- `reject if`: no match may satisfy the expressions. -/
  | reject
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A check: a disjunction of queries that must succeed. -/
structure Check where
  /-- The queries; the check succeeds if any of them does. -/
  queries : List Rule
  /-- Which flavour of check this is. -/
  kind : CheckKind
  deriving Repr, Inhabited

/-- Whether a policy allows or denies. -/
inductive PolicyKind where
  /-- Authorization succeeds when this policy matches. -/
  | allow
  /-- Authorization fails when this policy matches. -/
  | deny
  deriving Repr, DecidableEq, Inhabited, BEq

/-- An allow or deny policy, only ever provided by the authorizer. -/
structure Policy where
  /-- The queries; the policy matches if any of them does. -/
  queries : List Rule
  /-- Whether matching allows or denies. -/
  kind : PolicyKind
  deriving Repr, Inhabited

namespace Predicate

/-- The variables occurring in a predicate's arguments. -/
def variables (p : Predicate) : List Nat :=
  p.terms.filterMap fun
    | .variable i => some i
    | _ => none

end Predicate

namespace Rule

/-- The set of variables occurring in the rule's body, in order of first
appearance. -/
def bodyVariables (r : Rule) : List Nat :=
  r.body.foldl (fun acc p => p.variables.foldl (fun acc v =>
    if acc.contains v then acc else acc ++ [v]) acc) []

/-- The variables of the head that are not bound by the body.  A rule is safe
exactly when this is empty. -/
def unboundHeadVariables (r : Rule) : List Nat :=
  let bound := r.bodyVariables
  r.head.variables.foldl (fun acc v =>
    if bound.contains v || acc.contains v then acc else acc ++ [v]) []

end Rule

end Datalog
end LeanBiscuit
