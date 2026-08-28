import LeanBiscuit.Util.Bytes

/-!
# Datalog terms

A term is the datalog value type: the arguments of predicates and the values
manipulated by expressions.  Strings are interned, so a `str` term carries an
index into the token's symbol table rather than the characters themselves.

Sets and maps are kept in a canonical form — sorted, and deduplicated by key —
so that structural equality on the Lean representation coincides with the
mathematical equality of the values, and so that printing is deterministic.
The ordering is the one the reference implementation derives, since it is
observable: it decides the order in which set elements are printed.
-/

namespace LeanBiscuit
namespace Datalog

/-- The key of a map entry: either an integer or an interned string. -/
inductive MapKey where
  /-- An integer key. -/
  | integer (value : Int)
  /-- An interned string key. -/
  | str (index : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A datalog term. -/
inductive Term where
  /-- A variable, identified by an interned name.  Only legal inside rules. -/
  | variable (index : Nat)
  /-- A signed 64 bit integer. -/
  | integer (value : Int)
  /-- An interned string. -/
  | str (index : Nat)
  /-- A date, as seconds since the Unix epoch. -/
  | date (value : Nat)
  /-- A byte string. -/
  | bytes (value : Bytes)
  /-- A boolean. -/
  | bool (value : Bool)
  /-- A set: sorted and deduplicated. -/
  | set (elements : List Term)
  /-- The absence of a value. -/
  | null
  /-- An ordered list of terms. -/
  | array (elements : List Term)
  /-- A map: entries sorted by key, keys unique. -/
  | map (entries : List (MapKey × Term))
  deriving Repr, Inhabited

namespace MapKey

/-- Ordering: integers before strings, matching the derived order of the
reference implementation. -/
def compare : MapKey → MapKey → Ordering
  | .integer a, .integer b => Ord.compare a b
  | .integer _, .str _ => .lt
  | .str _, .integer _ => .gt
  | .str a, .str b => Ord.compare a b

instance : Ord MapKey := ⟨compare⟩

end MapKey

namespace Term

/-- The index of a term's constructor, which is the primary sort key. -/
def tag : Term → Nat
  | .variable _ => 0
  | .integer _ => 1
  | .str _ => 2
  | .date _ => 3
  | .bytes _ => 4
  | .bool _ => 5
  | .set _ => 6
  | .null => 7
  | .array _ => 8
  | .map _ => 9

mutual

/-- Total ordering on terms, matching the order derived by the reference
implementation (constructor order first, then payload). -/
def compare : Term → Term → Ordering
  | .variable a, .variable b => Ord.compare a b
  | .integer a, .integer b => Ord.compare a b
  | .str a, .str b => Ord.compare a b
  | .date a, .date b => Ord.compare a b
  | .bytes a, .bytes b => Bytes.compare a b
  | .bool a, .bool b => Ord.compare (if a then 1 else 0) (if b then 1 else 0)
  | .set a, .set b => compareList a b
  | .null, .null => .eq
  | .array a, .array b => compareList a b
  | .map a, .map b => compareEntries a b
  | a, b => Ord.compare a.tag b.tag

/-- Lexicographic ordering of term lists; a proper prefix is smaller. -/
def compareList : List Term → List Term → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match compare a b with
    | .eq => compareList as bs
    | o => o

/-- Lexicographic ordering of map entry lists. -/
def compareEntries : List (MapKey × Term) → List (MapKey × Term) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (ka, va) :: as, (kb, vb) :: bs =>
    match MapKey.compare ka kb with
    | .eq => match compare va vb with
             | .eq => compareEntries as bs
             | o => o
    | o => o

end

instance : Ord Term := ⟨compare⟩

instance : BEq Term := ⟨fun a b => compare a b == .eq⟩

/-- Structural equality, defined through the ordering. -/
def beq (a b : Term) : Bool := compare a b == .eq

end Term

/-- Insert into a sorted, deduplicated list of terms. -/
def sortedInsert (t : Term) : List Term → List Term
  | [] => [t]
  | x :: xs =>
    match Term.compare t x with
    | .lt => t :: x :: xs
    | .eq => x :: xs
    | .gt => x :: sortedInsert t xs

/-- Build the canonical (sorted, deduplicated) form of a set from a list. -/
def mkSet (l : List Term) : List Term := l.foldl (fun acc t => sortedInsert t acc) []

/-- Insert into a list of map entries kept sorted by key; a later value for an
existing key replaces the earlier one, as `BTreeMap::insert` does. -/
def entryInsert (k : MapKey) (v : Term) : List (MapKey × Term) → List (MapKey × Term)
  | [] => [(k, v)]
  | (k', v') :: xs =>
    match MapKey.compare k k' with
    | .lt => (k, v) :: (k', v') :: xs
    | .eq => (k, v) :: xs
    | .gt => (k', v') :: entryInsert k v xs

/-- Build the canonical form of a map from a list of entries. -/
def mkMap (l : List (MapKey × Term)) : List (MapKey × Term) :=
  l.foldl (fun acc (k, v) => entryInsert k v acc) []

/-- Is `t` a member of the canonical set `s`? -/
def setContains (s : List Term) (t : Term) : Bool := s.any (Term.beq t)

/-- Set intersection, preserving the canonical form. -/
def setIntersection (a b : List Term) : List Term := a.filter (setContains b)

/-- Set union, preserving the canonical form. -/
def setUnion (a b : List Term) : List Term := b.foldl (fun acc t => sortedInsert t acc) a

/-- Is `a` a superset of `b`? -/
def setIsSuperset (a b : List Term) : Bool := b.all (setContains a)

/-- The lower and upper bounds of the signed 64 bit integers, which is the range
datalog integers live in. -/
def int64Min : Int := -9223372036854775808

/-- The largest signed 64 bit integer. -/
def int64Max : Int := 9223372036854775807

/-- Does `i` fit in a signed 64 bit integer? -/
def inInt64Range (i : Int) : Bool := int64Min ≤ i && i ≤ int64Max

end Datalog
end LeanBiscuit
