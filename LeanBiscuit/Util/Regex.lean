/-!
# Regular expressions

The datalog `matches` operation runs a regular expression search over a string.
This module provides a small, total engine: patterns are parsed into an AST,
compiled to a Thompson NFA, and simulated as a set of active states.  The
simulation visits each input position once, so it always terminates and needs no
backtracking budget.

The supported syntax is the common subset: literals, `.`, character classes with
ranges and negation, the shorthands `\d \D \w \W \s \S`, grouping (capturing and
`(?:` non-capturing), alternation, the quantifiers `*`, `+`, `?` and `{n,m}`,
the anchors `^` and `$`, and the word boundaries `\b` and `\B`.  A search is
unanchored, matching the `is_match` semantics of the reference implementation.
-/

namespace LeanBiscuit
namespace Regex

/-- A character class: a set of ranges, optionally complemented. -/
structure CharClass where
  /-- Is the class complemented? -/
  negated : Bool
  /-- Inclusive ranges of code points. -/
  ranges : List (Char × Char)
  deriving Repr, Inhabited

namespace CharClass

/-- Does `c` belong to the class? -/
def contains (cl : CharClass) (c : Char) : Bool :=
  let inRanges := cl.ranges.any fun (lo, hi) => lo ≤ c && c ≤ hi
  if cl.negated then !inRanges else inRanges

/-- The class of a single character. -/
def single (c : Char) : CharClass := ⟨false, [(c, c)]⟩

/-- `.`: any character except a newline. -/
def dot : CharClass := ⟨true, [('\n', '\n')]⟩

/-- `\d`. -/
def digit : CharClass := ⟨false, [('0', '9')]⟩

/-- `\w`. -/
def word : CharClass := ⟨false, [('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]⟩

/-- `\s`. -/
def space : CharClass := ⟨false, [(' ', ' '), ('\t', '\t'), ('\n', '\n'),
                                  ('\r', '\r'), (Char.ofNat 11, Char.ofNat 12)]⟩

/-- Complement a class. -/
def negate (cl : CharClass) : CharClass := { cl with negated := !cl.negated }

end CharClass

/-- A parsed pattern. -/
inductive Ast where
  /-- Matches the empty string. -/
  | empty
  /-- Matches one character of a class. -/
  | cls (c : CharClass)
  /-- Sequencing. -/
  | concat (a b : Ast)
  /-- Alternation. -/
  | alt (a b : Ast)
  /-- Zero or more repetitions. -/
  | star (a : Ast)
  /-- One or more repetitions. -/
  | plus (a : Ast)
  /-- Zero or one repetition. -/
  | opt (a : Ast)
  /-- Between `min` and `max` repetitions; `none` means unbounded. -/
  | rep (a : Ast) (min : Nat) (max : Option Nat)
  /-- Start of text. -/
  | startAnchor
  /-- End of text. -/
  | endAnchor
  /-- A word boundary, or its complement. -/
  | wordBoundary (negated : Bool)
  deriving Repr, Inhabited

/-! ## Parsing -/

namespace Parser

/-- Characters that must be escaped to be taken literally. -/
def isMeta (c : Char) : Bool :=
  c == '.' || c == '*' || c == '+' || c == '?' || c == '(' || c == ')' ||
  c == '[' || c == ']' || c == '{' || c == '}' || c == '|' || c == '^' ||
  c == '$' || c == '\\'

/-- Interpret an escape sequence outside a character class. -/
def escapeAtom (c : Char) : Option Ast :=
  match c with
  | 'd' => some (.cls CharClass.digit)
  | 'D' => some (.cls CharClass.digit.negate)
  | 'w' => some (.cls CharClass.word)
  | 'W' => some (.cls CharClass.word.negate)
  | 's' => some (.cls CharClass.space)
  | 'S' => some (.cls CharClass.space.negate)
  | 'b' => some (.wordBoundary false)
  | 'B' => some (.wordBoundary true)
  | 'n' => some (.cls (CharClass.single '\n'))
  | 'r' => some (.cls (CharClass.single '\r'))
  | 't' => some (.cls (CharClass.single '\t'))
  | c => if isMeta c || !c.isAlphanum then some (.cls (CharClass.single c)) else none

/-- One item inside a character class: either a shorthand class or a literal. -/
inductive ClassItem where
  /-- A shorthand such as `\d`. -/
  | shorthand (c : CharClass)
  /-- A literal character. -/
  | lit (c : Char)
  deriving Repr

/-- Interpret an escape sequence inside a character class. -/
def escapeClassItem (c : Char) : Option ClassItem :=
  match c with
  | 'd' => some (.shorthand CharClass.digit)
  | 'D' => some (.shorthand CharClass.digit.negate)
  | 'w' => some (.shorthand CharClass.word)
  | 'W' => some (.shorthand CharClass.word.negate)
  | 's' => some (.shorthand CharClass.space)
  | 'S' => some (.shorthand CharClass.space.negate)
  | 'n' => some (.lit '\n')
  | 'r' => some (.lit '\r')
  | 't' => some (.lit '\t')
  | c => some (.lit c)

/-- Expand a shorthand class into ranges, refusing complemented shorthands
inside a class (which would need a general set algebra). -/
def shorthandRanges : CharClass → Option (List (Char × Char))
  | ⟨false, r⟩ => some r
  | ⟨true, _⟩ => none

/-- Parse the body of a character class, after the opening bracket. -/
def parseClassBody (cs : List Char) : Option (CharClass × List Char) :=
  let (negated, cs) := match cs with
    | '^' :: rest => (true, rest)
    | _ => (false, cs)
  -- a `]` in first position is a literal
  let (initial, cs) := match cs with
    | ']' :: rest => ([(']', ']')], rest)
    | _ => ([], cs)
  let rec go (cs : List Char) (acc : List (Char × Char)) (fuel : Nat) :
      Option (List (Char × Char) × List Char) :=
    match fuel, cs with
    | 0, _ => none
    | _, [] => none
    | _, ']' :: rest => some (acc, rest)
    | fuel + 1, c :: rest => do
      let (item, rest) ←
        if c == '\\' then
          match rest with
          | e :: rest => do let i ← escapeClassItem e; pure (i, rest)
          | [] => none
        else pure (ClassItem.lit c, rest)
      match item with
      | .shorthand cl => do
        let rs ← shorthandRanges cl
        go rest (acc ++ rs) fuel
      | .lit c₁ =>
        match rest with
        | '-' :: c₂ :: rest' =>
          if c₂ == ']' then go rest (acc ++ [(c₁, c₁), ('-', '-')]) fuel
          else
            let (c₂, rest') :=
              if c₂ == '\\' then
                match rest' with
                | e :: r => (e, r)
                | [] => (c₂, rest')
              else (c₂, rest')
            if c₁ ≤ c₂ then go rest' (acc ++ [(c₁, c₂)]) fuel else none
        | _ => go rest (acc ++ [(c₁, c₁)]) fuel
  match go cs initial (cs.length + 1) with
  | some (ranges, rest) => some (⟨negated, ranges⟩, rest)
  | none => none

/-- Parse a decimal number. -/
def parseNat (cs : List Char) : Option (Nat × List Char) :=
  let digits := cs.takeWhile Char.isDigit
  if digits.isEmpty then none
  else some (digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0,
             cs.drop digits.length)

mutual

/-- Parse an alternation, the outermost level. -/
def parseAlt (cs : List Char) (fuel : Nat) : Option (Ast × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (first, rest) ← parseConcat cs fuel
    match rest with
    | '|' :: rest => do
      let (second, rest) ← parseAlt rest fuel
      pure (.alt first second, rest)
    | _ => pure (first, rest)

/-- Parse a sequence of quantified atoms. -/
def parseConcat (cs : List Char) (fuel : Nat) : Option (Ast × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | [] => some (.empty, [])
    | ')' :: _ | '|' :: _ => some (.empty, cs)
    | _ => do
      let (a, rest) ← parseRepeat cs fuel
      let (b, rest) ← parseConcat rest fuel
      pure (match b with | .empty => a | b => .concat a b, rest)

/-- Parse an atom followed by any quantifiers. -/
def parseRepeat (cs : List Char) (fuel : Nat) : Option (Ast × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (a, rest) ← parseAtom cs fuel
    parsePostfix a rest fuel

/-- Apply postfix quantifiers to an already parsed atom. -/
def parsePostfix (a : Ast) (cs : List Char) (fuel : Nat) : Option (Ast × List Char) :=
  match fuel with
  | 0 => some (a, cs)
  | fuel + 1 =>
    -- a trailing `?` only selects lazy matching, which cannot change whether a
    -- match exists, so it is consumed and ignored
    let dropLazy (cs : List Char) := match cs with | '?' :: r => r | _ => cs
    match cs with
    | '*' :: rest => parsePostfix (.star a) (dropLazy rest) fuel
    | '+' :: rest => parsePostfix (.plus a) (dropLazy rest) fuel
    | '?' :: rest => parsePostfix (.opt a) (dropLazy rest) fuel
    | '{' :: rest =>
      match parseNat rest with
      | none => some (a, cs)
      | some (min, rest) =>
        match rest with
        | '}' :: rest => parsePostfix (.rep a min (some min)) (dropLazy rest) fuel
        | ',' :: '}' :: rest => parsePostfix (.rep a min none) (dropLazy rest) fuel
        | ',' :: rest =>
          match parseNat rest with
          | none => none
          | some (max, rest) =>
            match rest with
            | '}' :: rest =>
              if max < min then none
              else parsePostfix (.rep a min (some max)) (dropLazy rest) fuel
            | _ => none
        | _ => none
    | _ => some (a, cs)

/-- Parse a single atom. -/
def parseAtom (cs : List Char) (fuel : Nat) : Option (Ast × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | [] => none
    | '(' :: rest =>
      let rest := match rest with
        | '?' :: ':' :: r => r
        | r => r
      do
        let (inner, rest) ← parseAlt rest fuel
        match rest with
        | ')' :: rest => pure (inner, rest)
        | _ => none
    | '[' :: rest => do
      let (cl, rest) ← parseClassBody rest
      pure (.cls cl, rest)
    | '.' :: rest => some (.cls CharClass.dot, rest)
    | '^' :: rest => some (.startAnchor, rest)
    | '$' :: rest => some (.endAnchor, rest)
    | '\\' :: e :: rest => do
      let a ← escapeAtom e
      pure (a, rest)
    | '\\' :: [] => none
    | c :: rest =>
      if c == '*' || c == '+' || c == '?' || c == ')' then none
      else some (.cls (CharClass.single c), rest)

end

/-- Parse a whole pattern. -/
def parse (pattern : String) : Option Ast :=
  let cs := pattern.toList
  match parseAlt cs (cs.length * 2 + 2) with
  | some (a, []) => some a
  | _ => none

end Parser

/-! ## Compilation and simulation -/

/-- One NFA instruction. -/
inductive Inst where
  /-- Consume a character of the class, then continue at `next`. -/
  | chr (cls : CharClass) (next : Nat)
  /-- Continue at either branch. -/
  | split (a b : Nat)
  /-- Continue at `next`. -/
  | jmp (next : Nat)
  /-- Continue at `next` only at the start of the input. -/
  | assertStart (next : Nat)
  /-- Continue at `next` only at the end of the input. -/
  | assertEnd (next : Nat)
  /-- Continue at `next` only at a (possibly negated) word boundary. -/
  | assertWordBoundary (negated : Bool) (next : Nat)
  /-- The pattern has matched. -/
  | accept
  deriving Repr, Inhabited

/-- A compiled pattern. -/
structure Program where
  /-- The instructions, indexed by state number. -/
  insts : Array Inst
  /-- The entry state. -/
  start : Nat
  deriving Repr, Inhabited

namespace Ast

/-- A size measure for compilation.  A bounded repetition counts as larger than
the `star` it expands into, which is what makes compilation terminate. -/
def size : Ast → Nat
  | .empty | .cls _ | .startAnchor | .endAnchor | .wordBoundary _ => 1
  | .concat a b => 1 + a.size + b.size
  | .alt a b => 1 + a.size + b.size
  | .star a => 1 + a.size
  | .plus a => 1 + a.size
  | .opt a => 1 + a.size
  | .rep a _ _ => 2 + a.size

end Ast

namespace Compile

/-- Append an instruction, returning its index. -/
def push (insts : Array Inst) (i : Inst) : Nat × Array Inst :=
  (insts.size, insts.push i)

mutual

/-- Compile `a` so that it continues at `next`, returning the entry state. -/
def go (a : Ast) (next : Nat) (insts : Array Inst) : Nat × Array Inst :=
  match a with
  | .empty => (next, insts)
  | .cls c => push insts (.chr c next)
  | .startAnchor => push insts (.assertStart next)
  | .endAnchor => push insts (.assertEnd next)
  | .wordBoundary n => push insts (.assertWordBoundary n next)
  | .concat x y =>
    let (entryY, insts) := go y next insts
    go x entryY insts
  | .alt x y =>
    let (entryX, insts) := go x next insts
    let (entryY, insts) := go y next insts
    push insts (.split entryX entryY)
  | .opt x =>
    let (entryX, insts) := go x next insts
    push insts (.split entryX next)
  | .star x =>
    -- the hole is patched once the body is compiled, closing the loop
    let (hole, insts) := push insts (.jmp next)
    let (entryX, insts) := go x hole insts
    (hole, insts.set! hole (.split entryX next))
  | .plus x =>
    let (hole, insts) := push insts (.jmp next)
    let (entryX, insts) := go x hole insts
    (entryX, insts.set! hole (.split entryX next))
  | .rep x min max =>
    match max with
    | none =>
      -- `x{n,}` is `n` copies followed by `x*`
      let (tail, insts) := go (.star x) next insts
      exactly x min tail insts
    | some m =>
      -- `x{n,m}` is `n` copies followed by `m - n` optional copies
      let (tail, insts) := optional x (m - min) next insts
      exactly x min tail insts
termination_by (a.size, 1, 0)
decreasing_by all_goals (try simp only [Ast.size]) <;> first | omega | decreasing_tactic

/-- Compile `n` copies of `a` in sequence, ending at `next`. -/
def exactly (a : Ast) (n : Nat) (next : Nat) (insts : Array Inst) : Nat × Array Inst :=
  match n with
  | 0 => (next, insts)
  | n + 1 =>
    let (entry, insts) := go a next insts
    exactly a n entry insts
termination_by (a.size + 1, 0, n)
decreasing_by all_goals (try simp only [Ast.size]) <;> first | omega | decreasing_tactic

/-- Compile `n` optional copies of `a` in sequence, ending at `next`. -/
def optional (a : Ast) (n : Nat) (next : Nat) (insts : Array Inst) : Nat × Array Inst :=
  match n with
  | 0 => (next, insts)
  | n + 1 =>
    let (entry, insts) := go a next insts
    let (branch, insts) := push insts (.split entry next)
    optional a n branch insts
termination_by (a.size + 1, 0, n)
decreasing_by all_goals (try simp only [Ast.size]) <;> first | omega | decreasing_tactic

end

end Compile

/-- Compile a pattern AST into a program. -/
def compile (a : Ast) : Program :=
  let (accept, insts) := Compile.push #[] .accept
  let (start, insts) := Compile.go a accept insts
  ⟨insts, start⟩

/-- Is `c` a word character? -/
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Where in the input the simulation currently is, which decides whether the
zero-width assertions hold. -/
structure Position where
  /-- Is this the start of the input? -/
  atStart : Bool
  /-- Is this the end of the input? -/
  atEnd : Bool
  /-- Is this a word boundary? -/
  isBoundary : Bool
  deriving Repr, Inhabited

/-- The states directly reachable from `pc` without consuming input. -/
def epsilonStep (prog : Program) (pos : Position) (pc : Nat) : List Nat :=
  match prog.insts[pc]! with
  | .split a b => [a, b]
  | .jmp n => [n]
  | .assertStart n => if pos.atStart then [n] else []
  | .assertEnd n => if pos.atEnd then [n] else []
  | .assertWordBoundary negated n => if pos.isBoundary != negated then [n] else []
  | .chr _ _ | .accept => []

/-- Saturate `visited` under epsilon transitions, working through `frontier`.

Each round either drops an already visited state or marks a new one, so the
number of rounds is bounded by the size of the program. -/
def saturate (prog : Program) (pos : Position) (visited : Array Bool) (frontier : List Nat)
    (fuel : Nat) : Array Bool :=
  match fuel, frontier with
  | _, [] => visited
  | 0, _ => visited
  | fuel + 1, pc :: rest =>
    if visited[pc]! then saturate prog pos visited rest fuel
    else saturate prog pos (visited.set! pc true) (epsilonStep prog pos pc ++ rest) fuel

/-- The epsilon closure of `seeds`, as the set of states it can reach. -/
def closure (prog : Program) (pos : Position) (seeds : List Nat) : Array Bool :=
  saturate prog pos (Array.replicate prog.insts.size false) seeds
    (seeds.length + 3 * prog.insts.size + 1)

/-- The states of a closure that consume input or accept. -/
def activeStates (prog : Program) (visited : Array Bool) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for pc in [0:prog.insts.size] do
    if visited[pc]! then
      match prog.insts[pc]! with
      | .chr _ _ | .accept => out := out.push pc
      | _ => pure ()
  return out

/-- Does the active set contain an accepting state? -/
def hasAccept (prog : Program) (active : Array Nat) : Bool :=
  active.any fun pc => match prog.insts[pc]! with
    | .accept => true
    | _ => false

/-- Run the simulation from one position onwards.

The start state is re-added at every position, which is what makes the search
unanchored: a match may begin anywhere. -/
def step (prog : Program) (cs : List Char) (prev : Option Char) (pending : List Nat)
    (atStart : Bool) : Bool :=
  let isBoundary :=
    match prev, cs.head? with
    | none, none => false
    | none, some c => isWordChar c
    | some p, none => isWordChar p
    | some p, some c => isWordChar p != isWordChar c
  let pos : Position := { atStart, atEnd := cs.isEmpty, isBoundary }
  let active := activeStates prog (closure prog pos (prog.start :: pending))
  if hasAccept prog active then true
  else
    match cs with
    | [] => false
    | c :: rest =>
      let next := active.foldl (fun acc pc =>
        match prog.insts[pc]! with
        | .chr cl target => if cl.contains c then acc.push target else acc
        | _ => acc) (#[] : Array Nat)
      step prog rest (some c) next.toList false

/-- Does the program match anywhere in the input? -/
def run (prog : Program) (input : List Char) : Bool := step prog input none [] true

/-- Does `pattern` match anywhere in `s`?  An invalid pattern never matches,
which is how the reference implementation treats one. -/
def isMatch (pattern : String) (s : String) : Bool :=
  match Parser.parse pattern with
  | none => false
  | some ast => run (compile ast) s.toList

end Regex
end LeanBiscuit
