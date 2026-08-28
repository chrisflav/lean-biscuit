import LeanBiscuit

/-!
# The `lean-biscuit` command line tool

Inspects, verifies and authorizes biscuit tokens.  A token is read either from a
file of raw bytes or, with `--base64`, from a file holding its URL-safe base64
text form.
-/

open LeanBiscuit LeanBiscuit.Token LeanBiscuit.Datalog

/-- Usage text. -/
def usage : String :=
"lean-biscuit — a biscuit token implementation

usage:
  lean-biscuit inspect <token> [--base64]
      print a token's blocks without verifying its signatures

  lean-biscuit verify <token> <root-public-key> [--base64]
      verify the signature chain against a root public key

  lean-biscuit authorize <token> <root-public-key> <authorizer.datalog> [--base64]
      verify a token, then authorize it with the datalog in the given file

a root public key is written as `ed25519/<hex>` or `secp256r1/<hex>`."

/-- Parse a public key written as `ed25519/<hex>` or `secp256r1/<hex>`. -/
def parsePublicKey (s : String) : Except String PublicKey := do
  let (algorithm, hex) ←
    if s.startsWith "ed25519/" then pure (Algorithm.ed25519, (s.drop "ed25519/".length).toString)
    else if s.startsWith "secp256r1/" then
      pure (Algorithm.secp256r1, (s.drop "secp256r1/".length).toString)
    else throw "a public key must be written as `ed25519/<hex>` or `secp256r1/<hex>`"
  let some bytes := Bytes.ofHex? hex | throw "the key is not valid hexadecimal"
  match PublicKey.ofBytes algorithm bytes with
  | .ok k => pure k
  | .error _ => throw "the key has the wrong length for its algorithm"

/-- Read a token from a file, either raw or base64 encoded. -/
def readToken (path : String) (base64 : Bool) : IO Bytes := do
  if base64 then
    let text := (← IO.FS.readFile path).trimAscii.toString
    let text := if text.startsWith "biscuit:" then (text.drop "biscuit:".length).toString
                else text
    match Base64.decode? text with
    | some b => pure b
    | none => throw (IO.userError "the token is not valid URL-safe base64")
  else IO.FS.readBinFile path

/-- Print a token's blocks as datalog. -/
def printToken (token : Biscuit) : IO Unit := do
  for (block, i) in token.blocks.zipIdx do
    -- a third-party block is written against its own symbol table
    let symbols := if block.externalKey.isSome && i != 0 then block.symbols else token.symbols
    let header := if i == 0 then "authority" else s!"block {i}"
    let signer := match block.externalKey with
      | some k => s!" (signed by {k.print})"
      | none => ""
    IO.println s!"// {header}{signer}, datalog v3.{block.version - 3}"
    match block.context with
    | some c => IO.println s!"// context: {c}"
    | none => pure ()
    if !block.scopes.isEmpty then
      IO.println ("trusting " ++ String.intercalate ", " (block.scopes.map (printScope symbols))
        ++ ";")
    for f in block.facts do IO.println (printFact symbols f ++ ";")
    for r in block.rules do IO.println (printRule symbols r ++ ";")
    for c in block.checks do IO.println (printCheck symbols c ++ ";")
    IO.println ""
  IO.println "// revocation identifiers"
  for (id, i) in token.revocationIdentifiers.zipIdx do
    IO.println s!"//   {i}: {Bytes.toHex id}"

/-- Report a failure and exit with a non-zero status. -/
def die (message : String) : IO UInt32 := do
  IO.eprintln message
  pure 1

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  let base64 := args.contains "--base64"
  let args := args.filter (· != "--base64")
  match args with
  | ["inspect", path] => do
    let data ← readToken path base64
    match Biscuit.ofBytesUnverified data with
    | .error e => die s!"could not read the token: {e}"
    | .ok token => do
      IO.println "// NOTE: signatures were not verified"
      printToken token
      pure 0
  | ["verify", path, key] => do
    let data ← readToken path base64
    match parsePublicKey key with
    | .error e => die e
    | .ok root =>
      match Biscuit.ofBytes data root with
      | .error e => die s!"the token did not verify: {e}"
      | .ok token => do
        IO.println s!"the token verifies, with {token.blockCount} block(s)"
        IO.println (if token.isSealed then "it is sealed" else "it can still be attenuated")
        pure 0
  | ["authorize", path, key, authorizerPath] => do
    let data ← readToken path base64
    let code ← IO.FS.readFile authorizerPath
    match parsePublicKey key with
    | .error e => die e
    | .ok root =>
      match Biscuit.ofBytes data root with
      | .error e => die s!"the token did not verify: {e}"
      | .ok token =>
        match AuthorizerBuilder.code {} code with
        | .error e => die s!"could not parse the authorizer: {e}"
        | .ok builder =>
          match Authorizer.authorizeToken builder token with
          | .ok i => do IO.println s!"authorized by policy {i}"; pure 0
          | .error e => die s!"{e}"
  | _ => do IO.println usage; pure (if args.isEmpty then 0 else 1)
