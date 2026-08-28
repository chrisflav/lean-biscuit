import Tests.Samples
import Tests.RoundTrip

/-!
# Test entry point

Runs the conformance suite over the specification's sample tokens, then the
round-trip and known-answer tests.
-/

/-- Run every test suite, reporting failures on standard error. -/
def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := match args with
    | [] => "samples/current"
    | d :: _ => d
  let (count, sampleFailures) ← LeanBiscuit.Tests.run dir
  let roundTripFailures ← LeanBiscuit.Tests.runRoundTrip dir
  for f in sampleFailures ++ roundTripFailures do
    IO.eprintln f
  if sampleFailures.isEmpty && roundTripFailures.isEmpty then
    IO.println s!"all {count} sample validations passed"
    IO.println "all round-trip and known-answer tests passed"
    pure 0
  else
    IO.eprintln s!"{sampleFailures.length} of {count} sample validations failed"
    IO.eprintln s!"{roundTripFailures.length} round-trip tests failed"
    pure 1
