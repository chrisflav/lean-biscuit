/-!
# Dates

Datalog dates are counts of seconds since the Unix epoch, but their source and
printed forms are RFC 3339 timestamps.  This module converts between the two,
using Howard Hinnant's `days_from_civil` / `civil_from_days` algorithms, which
are exact for the whole proleptic Gregorian calendar.
-/

namespace LeanBiscuit
namespace Time

/-- Integer division rounding towards negative infinity. -/
def fdiv (a b : Int) : Int := if a ≥ 0 then a / b else -((-a + b - 1) / b)

/-- Is `y` a leap year in the proleptic Gregorian calendar? -/
def isLeapYear (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- The number of days from 1970-01-01 to the given civil date. -/
def daysFromCivil (y : Int) (m : Nat) (d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := fdiv y 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy := (153 * mp + 2) / 5 + (d : Int) - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The civil date `days` days after 1970-01-01. -/
def civilFromDays (days : Int) : Int × Nat × Nat :=
  let z := days + 719468
  let era := fdiv z 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := if m ≤ 2 then y + 1 else y
  (y, m.toNat, d.toNat)

/-- Left-pad the decimal representation of `n` to `width` digits. -/
def pad (width : Nat) (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (width - s.length) ++ s

/-- Render a Unix timestamp as an RFC 3339 timestamp in UTC.

Returns `none` when the year falls outside the four-digit range RFC 3339 can
represent, which is what the reference implementation reports as an invalid
date. -/
def formatRfc3339 (timestamp : Int) : Option String :=
  let days := fdiv timestamp 86400
  let secondsOfDay := (timestamp - days * 86400).toNat
  let (y, m, d) := civilFromDays days
  if y < 0 || y > 9999 then none
  else
    let hh := secondsOfDay / 3600
    let mm := secondsOfDay % 3600 / 60
    let ss := secondsOfDay % 60
    some s!"{pad 4 y.toNat}-{pad 2 m}-{pad 2 d}T{pad 2 hh}:{pad 2 mm}:{pad 2 ss}Z"

/-- Parse a run of exactly `n` decimal digits from `cs`, returning the value and
the rest. -/
def takeDigits (n : Nat) (cs : List Char) : Option (Nat × List Char) :=
  let rec go (n : Nat) (cs : List Char) (acc : Nat) : Option (Nat × List Char) :=
    match n, cs with
    | 0, cs => some (acc, cs)
    | n + 1, c :: rest =>
      if c.isDigit then go n rest (acc * 10 + (c.toNat - '0'.toNat)) else none
    | _, [] => none
  go n cs 0

/-- Parse an RFC 3339 timestamp into a Unix timestamp.

Accepts an optional fractional part (which is discarded, as datalog dates have
one second resolution) and either `Z` or a numeric UTC offset. -/
def parseRfc3339 (s : String) : Option Int := do
  let cs := s.toList
  let (year, cs) ← takeDigits 4 cs
  let cs ← match cs with | '-' :: r => some r | _ => none
  let (month, cs) ← takeDigits 2 cs
  let cs ← match cs with | '-' :: r => some r | _ => none
  let (day, cs) ← takeDigits 2 cs
  let cs ← match cs with | 'T' :: r => some r | 't' :: r => some r | _ => none
  let (hour, cs) ← takeDigits 2 cs
  let cs ← match cs with | ':' :: r => some r | _ => none
  let (minute, cs) ← takeDigits 2 cs
  let cs ← match cs with | ':' :: r => some r | _ => none
  let (second, cs) ← takeDigits 2 cs
  -- an optional fractional part, which we drop
  let cs :=
    match cs with
    | '.' :: rest => rest.dropWhile Char.isDigit
    | _ => cs
  if month < 1 || month > 12 || day < 1 || day > 31 then none else
  if hour > 23 || minute > 59 || second > 60 then none else
  let daysInMonth : Nat :=
    match month with
    | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
    | 4 | 6 | 9 | 11 => 30
    | _ => if isLeapYear (year : Int) then 29 else 28
  if day > daysInMonth then none else
  let base := daysFromCivil (year : Int) month day * 86400
                + (hour : Int) * 3600 + (minute : Int) * 60 + (second : Int)
  match cs with
  | ['Z'] | ['z'] => some base
  | sign :: rest =>
    if sign != '+' && sign != '-' then none else do
      let (oh, rest) ← takeDigits 2 rest
      let rest ← match rest with | ':' :: r => some r | _ => none
      let (om, rest) ← takeDigits 2 rest
      if !rest.isEmpty then none else
      if oh > 23 || om > 59 then none else
      let offset := (oh : Int) * 3600 + (om : Int) * 60
      some (if sign == '+' then base - offset else base + offset)
  | [] => none

end Time
end LeanBiscuit
