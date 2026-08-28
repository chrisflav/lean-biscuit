import LeanBiscuit

/-!
# Round-trip and known-answer tests

The sample suite checks that this implementation agrees with the specification
when *reading* tokens.  This one checks the other direction — that tokens it
writes can be read back, by itself and in the same byte-for-byte encoding the
reference implementation produces — and pins down the primitives underneath with
published test vectors.
-/

open LeanBiscuit LeanBiscuit.Token LeanBiscuit.Datalog LeanBiscuit.Proto

namespace LeanBiscuit.Tests

/-- Comparing results is convenient in tests; `Except` has no `BEq` in core. -/
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- Accumulates the failures of a test run. -/
abbrev Failures := List String

/-- Record a failure unless the condition holds. -/
def expect (fs : Failures) (label : String) (condition : Bool) : Failures :=
  if condition then fs else fs ++ [label]

/-- Record a failure unless the two values are equal. -/
def expectEq [BEq α] [Repr α] (fs : Failures) (label : String) (actual expected : α) : Failures :=
  if actual == expected then fs
  else fs ++ [s!"{label}: expected {reprStr expected}, got {reprStr actual}"]

/-- A test key; the bytes are arbitrary. -/
def testKey (algorithm : Algorithm) (hex : String) : PrivateKey :=
  ⟨algorithm, (Bytes.ofHex? hex).getD Bytes.empty⟩

/-! ## Primitives -/

/-- Known-answer tests for the hashes, the signature schemes and the encodings. -/
def cryptoTests : Failures := Id.run do
  let mut fs : Failures := []
  let hx (s : String) : Bytes := (Bytes.ofHex? s).getD Bytes.empty
  -- FIPS 180-4
  fs := expectEq fs "sha256 of \"abc\"" (Bytes.toHex (Sha256.hash "abc".toUTF8))
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  fs := expectEq fs "sha512 of \"abc\"" (Bytes.toHex (Sha512.hash "abc".toUTF8))
    ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
      ++ "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
  -- RFC 4231-style HMAC check
  fs := expectEq fs "hmac-sha256"
    (Bytes.toHex (Hmac.sha256 "key".toUTF8 "The quick brown fox jumps over the lazy dog".toUTF8))
    "f7bc83f430538424b13298e6aa6fb143ef4d59a14946175997479dbc2d1a3cd8"
  -- RFC 8032 §7.1, test vector 3
  let ed25519Pub := hx "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025"
  let ed25519Sig := hx ("6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac"
    ++ "18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a")
  fs := expect fs "ed25519 verifies a valid signature"
    (Ed25519.verify ed25519Pub (hx "af82") ed25519Sig |>.toOption.isSome)
  fs := expect fs "ed25519 rejects a wrong message"
    (Ed25519.verify ed25519Pub (hx "af83") ed25519Sig |>.toOption.isNone)
  fs := expectEq fs "ed25519 derives the public key"
    ((Ed25519.publicKeyOfSecret
      (hx "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7")).map Bytes.toHex)
    (some "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025")
  fs := expectEq fs "ed25519 signs deterministically"
    ((Ed25519.sign (hx "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7")
      (hx "af82")).map Bytes.toHex) (some (Bytes.toHex ed25519Sig))
  -- RFC 6979 §A.2.5: P-256 with SHA-256 over "sample"
  let p256Secret := hx "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"
  fs := expectEq fs "p256 derives the public key"
    ((P256.publicKeyOfSecret p256Secret).map Bytes.toHex)
    (some "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6")
  match P256.sign p256Secret "sample".toUTF8 with
  | none => fs := fs ++ ["p256 failed to sign"]
  | some sig =>
    match P256.Der.parseSignature sig with
    | none => fs := fs ++ ["p256 produced an unparseable signature"]
    | some (r, _) =>
      fs := expectEq fs "p256 uses the RFC 6979 nonce" (Bytes.toHex (Bytes.ofNatBE 32 r))
        "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716"
    match P256.publicKeyOfSecret p256Secret with
    | none => fs := fs ++ ["p256 failed to derive a public key"]
    | some pub =>
      fs := expect fs "p256 verifies its own signature"
        (P256.verify pub "sample".toUTF8 sig |>.toOption.isSome)
      fs := expect fs "p256 rejects a wrong message"
        (P256.verify pub "sampl3".toUTF8 sig |>.toOption.isNone)
  -- encodings
  for s in ["", "f", "fo", "foo", "foob", "fooba", "foobar"] do
    fs := expectEq fs s!"base64 round trip of {s}"
      ((Base64.decode? (Base64.encode s.toUTF8)).map (·.toList)) (some s.toUTF8.toList)
  fs := expectEq fs "hex round trip" ((Bytes.ofHex? "00ff10ab").map Bytes.toHex) (some "00ff10ab")
  -- regular expressions, which the `matches` operation depends on
  fs := expect fs "regex matches a suffix" (Regex.isMatch "file[0-9]+.txt" "file123.txt")
  fs := expect fs "regex rejects a non-match" (!Regex.isMatch "file[0-9]+.txt" "file1")
  fs := expect fs "regex handles alternation and groups" (Regex.isMatch "^(ab)+c$" "ababc")
  fs := expect fs "regex anchors" (!Regex.isMatch "^abc$" "xabc")
  fs := expect fs "regex counts repetitions" (Regex.isMatch "a{2,3}" "aa")
  fs := expect fs "regex rejects too few repetitions" (!Regex.isMatch "a{2,3}b" "ab")
  fs := expect fs "an invalid pattern never matches" (!Regex.isMatch "[" "x")
  -- dates, whose textual form is part of the datalog syntax
  fs := expectEq fs "date round trip"
    ((Time.parseRfc3339 "2020-12-21T09:23:12Z").bind Time.formatRfc3339)
    (some "2020-12-21T09:23:12Z")
  fs := expectEq fs "date offsets are applied"
    (Time.parseRfc3339 "2022-12-04T09:46:41+01:00") (Time.parseRfc3339 "2022-12-04T08:46:41Z")
  pure fs

/-! ## The datalog text format -/

/-- Parsing then printing must reproduce the source, which is what makes the
printed form of a failed check meaningful. -/
def parserTests : Failures := Id.run do
  let sources := [
    "resource(\"file1\")",
    "right(\"file1\", \"read\")",
    "fact(null, 1, true, hex:12ab, 2020-12-21T09:23:12Z)",
    -- map keys print in their canonical order: integers before strings
    "fact({1, 2, 3}, [1, \"a\", null], {2: \"b\", \"a\": 1})"]
  let checks := [
    "check if resource($0), operation(\"read\"), right($0, \"read\")",
    "check all operation($op), allowed_operations($allowed), $allowed.contains($op)",
    "reject if test($test), $test",
    "check if 1 + 2 * 3 - 4 / 2 === 5",
    "check if 1 | 2 ^ 3 === 0",
    "check if !false && true, (true || false) && true",
    "check if {1, 2, 3}.any($p -> $p > 1 && {3, 4, 5}.any($q -> $p == $q))",
    "check if \"aaabde\".matches(\"a*c?.e\"), \"aaabde\".contains(\"abd\")",
    "check if (true === 12).try_or(true)",
    "check if true.extern::test(), \"a\".extern::test(\"a\") == \"equal strings\"",
    "check if query(1) trusting "
      ++ "ed25519/acdd6d5b53bfee478bf689f8e012fe7988bf755e3d7c5152947abc149bc20189",
    "check if resource($0) or resource($1)"]
  let rules := [
    "right($0, \"read\") <- resource($0), user_id($1), owner($1, $0)",
    "valid_date($1) <- time($0), resource($1), $0 <= 1999-12-31T12:59:59Z, "
      ++ "!{\"file1\"}.contains($1)"]
  let mut fs : Failures := []
  for s in sources do
    match Parser.parseAuthorizer (s ++ ";") with
    | .error e => fs := fs ++ [s!"failed to parse `{s}`: {e}"]
    | .ok r =>
      match r.facts with
      | [f] =>
        let (df, syms) := Builder.Fact.convert {} f
        fs := expectEq fs s!"fact round trip of `{s}`" (printFact syms df) s
      | _ => fs := fs ++ [s!"`{s}` did not parse as a single fact"]
  for s in checks do
    match Parser.parseAuthorizer (s ++ ";") with
    | .error e => fs := fs ++ [s!"failed to parse `{s}`: {e}"]
    | .ok r =>
      match r.checks with
      | [c] =>
        let (dc, syms) := Builder.Check.convert {} c
        fs := expectEq fs s!"check round trip of `{s}`" (printCheck syms dc) s
      | _ => fs := fs ++ [s!"`{s}` did not parse as a single check"]
  for s in rules do
    match Parser.parseAuthorizer (s ++ ";") with
    | .error e => fs := fs ++ [s!"failed to parse `{s}`: {e}"]
    | .ok r =>
      match r.rules with
      | [rl] =>
        let (dr, syms) := Builder.Rule.convert {} rl
        fs := expectEq fs s!"rule round trip of `{s}`" (printRule syms dr) s
      | _ => fs := fs ++ [s!"`{s}` did not parse as a single rule"]
  -- a rule whose head has a variable the body does not bind must be rejected
  fs := expect fs "an unsafe rule is rejected"
    (Parser.parseAuthorizer "operation($unbound, \"read\") <- operation($any1, $any2);"
      |>.toOption.isNone)
  -- comments are ignored
  fs := expect fs "comments are skipped"
    (match Parser.parseAuthorizer "// hello\nresource(\"a\"); /* and */ allow if true;" with
     | .ok r => r.facts.length == 1 && r.policies.length == 1
     | .error _ => false)
  pure fs

/-! ## Encoding -/

/-- Re-encoding every sample block must reproduce its original bytes, which
pins the protobuf encoding to the one the reference implementation writes. -/
def encodingTests (samplesDir : System.FilePath) : IO Failures := do
  let mut fs : Failures := []
  let entries ← samplesDir.readDir
  for entry in entries.qsort (fun a b => a.fileName < b.fileName) do
    if entry.fileName.endsWith ".bc" then
      let data ← IO.FS.readBinFile (samplesDir / entry.fileName)
      match Schema.decodeBiscuit data with
      | .error _ => pure ()
      | .ok container =>
        fs := expect fs s!"{entry.fileName}: container re-encodes identically"
          (Schema.encodeBiscuit container == data)
        for signed in container.authority :: container.blocks do
          match decodeBlock signed.block (signed.externalSignature.map (·.publicKey)) with
          | .error _ => pure ()
          | .ok block =>
            fs := expect fs s!"{entry.fileName}: block re-encodes identically"
              (encodeBlock block == signed.block)
  pure fs

/-! ## Creating, attenuating and sealing -/

/-- Build a token, attenuate it, seal it, and check that each step verifies and
authorizes as it should. -/
def tokenTests : Failures := Id.run do
  let mut fs : Failures := []
  let root := testKey .ed25519 "99e87b0e9158531eeeb503ff15266e2b23c2a2507b138c9d1b1f2ab458df2d61"
  let ephemeral := testKey .ed25519
    "1111111111111111111111111111111111111111111111111111111111111111"
  let ephemeral2 := testKey .ed25519
    "2222222222222222222222222222222222222222222222222222222222222222"
  let thirdParty := testKey .secp256r1
    "3333333333333333333333333333333333333333333333333333333333333333"
  let .ok rootPublic := root.publicKey | pure ["could not derive the root public key"]
  let .ok otherPublic := ephemeral.publicKey | pure ["could not derive a public key"]
  let .ok thirdPublic := thirdParty.publicKey | pure ["could not derive a public key"]
  fs := expectEq fs "the sample root key derives the sample public key" rootPublic.print
    "ed25519/1055c750b1a1505937af1537c626ba3263995c33a64758aaafb1275b0312e284"
  let .ok authority := BlockBuilder.code {}
    "right(\"file1\", \"read\");\nright(\"file2\", \"read\");"
    | pure ["could not parse the authority block"]
  let .ok token := Biscuit.create root ephemeral authority | pure ["could not create a token"]
  -- serialize, then read back and verify
  let .ok reparsed := Biscuit.ofBytes (Biscuit.toBytes token) rootPublic
    | pure ["a freshly created token did not verify"]
  fs := expectEq fs "a new token has one block" reparsed.blockCount 1
  fs := expect fs "a new token is not sealed" (!Biscuit.isSealed reparsed)
  let .ok fromText := Biscuit.ofBase64 (Biscuit.toBase64 token) rootPublic
    | pure ["the base64 form of a token did not verify"]
  fs := expectEq fs "base64 round trip preserves the token"
    (Bytes.toHex (Biscuit.toBytes fromText)) (Bytes.toHex (Biscuit.toBytes token))
  -- the wrong root key must reject it
  fs := expect fs "the wrong root key rejects the token"
    (Biscuit.ofBytes (Biscuit.toBytes token) otherPublic |>.toOption.isNone)
  -- tampering with the payload must be caught
  let raw := Biscuit.toBytes token
  let tampered := raw.set! (raw.size - 1) ((raw[raw.size - 1]!) ^^^ 1)
  fs := expect fs "a tampered token is rejected"
    (Biscuit.ofBytes tampered rootPublic |>.toOption.isNone)
  -- attenuate
  let .ok restriction := BlockBuilder.code {} "check if resource($r), right($r, \"read\");"
    | pure ["could not parse the attenuating block"]
  let .ok attenuated := Biscuit.append reparsed ephemeral2 restriction
    | pure ["could not attenuate the token"]
  let .ok attenuated := Biscuit.ofBytes (Biscuit.toBytes attenuated) rootPublic
    | pure ["an attenuated token did not verify"]
  fs := expectEq fs "attenuation adds a block" attenuated.blockCount 2
  let authorize (t : Token.Biscuit) (code : String) : Except TokenError Nat := do
    Authorizer.authorizeToken (← AuthorizerBuilder.code {} code) t
  fs := expectEq fs "the attenuated token allows a granted resource"
    (authorize attenuated "resource(\"file1\");\nallow if true;") (.ok 0)
  fs := expect fs "the attenuated token denies an ungranted resource"
    (authorize attenuated "resource(\"file3\");\nallow if true;" |>.toOption.isNone)
  fs := expect fs "no policy means no authorization"
    (authorize attenuated "resource(\"file1\");" |>.toOption.isNone)
  -- seal
  let .ok sealed := Biscuit.sealToken attenuated | pure ["could not seal the token"]
  let .ok sealed := Biscuit.ofBytes (Biscuit.toBytes sealed) rootPublic
    | pure ["a sealed token did not verify"]
  fs := expect fs "a sealed token reports itself sealed" (Biscuit.isSealed sealed)
  fs := expect fs "a sealed token cannot be attenuated"
    (Biscuit.append sealed ephemeral2 restriction |>.toOption.isNone)
  fs := expectEq fs "a sealed token still authorizes"
    (authorize sealed "resource(\"file1\");\nallow if true;") (.ok 0)
  -- a third-party block, signed by a key the authority names
  let .ok authority2 := BlockBuilder.code {}
    s!"right(\"file1\", \"read\");\ncheck if group(\"admin\") trusting {thirdPublic.print};"
    | pure ["could not parse the authority block"]
  let .ok token2 := Biscuit.create root ephemeral authority2
    | pure ["could not create a token"]
  fs := expect fs "the third-party check fails without the block"
    (authorize token2 "allow if true;" |>.toOption.isNone)
  let request := Biscuit.thirdPartyRequest token2
  let .ok thirdBlock := BlockBuilder.code {} "group(\"admin\");"
    | pure ["could not parse the third-party block"]
  let .ok contents := Biscuit.signThirdPartyBlock thirdParty request thirdBlock
    | pure ["could not sign a third-party block"]
  let .ok token3 := Biscuit.appendThirdParty token2 ephemeral2 contents
    | pure ["could not append a third-party block"]
  let .ok token3 := Biscuit.ofBytes (Biscuit.toBytes token3) rootPublic
    | pure ["a token with a third-party block did not verify"]
  fs := expectEq fs "the third-party block satisfies the check"
    (authorize token3 "allow if true;") (.ok 0)
  -- the same, rooted in a secp256r1 key
  let .ok token4 := Biscuit.create thirdParty ephemeral authority
    | pure ["could not create a secp256r1-rooted token"]
  let .ok token4 := Biscuit.ofBytes (Biscuit.toBytes token4) thirdPublic
    | pure ["a secp256r1-rooted token did not verify"]
  fs := expectEq fs "a secp256r1-rooted token authorizes"
    (authorize token4 "allow if true;") (.ok 0)
  -- an unverified read must still expose the contents
  fs := expect fs "an unverified read succeeds without the key"
    (Biscuit.ofBytesUnverified (Biscuit.toBytes token) |>.toOption.isSome)
  -- revocation identifiers are per block and distinct
  let ids := attenuated.revocationIdentifiers
  fs := expectEq fs "there is one revocation identifier per block" ids.length 2
  fs := expect fs "revocation identifiers differ between blocks"
    (Bytes.toHex ids[0]! != Bytes.toHex ids[1]!)
  pure fs

/-! ## Authorization behaviour -/

/-- Checks that exercise the parts of the engine the samples touch only
indirectly. -/
def engineTests : Failures := Id.run do
  let mut fs : Failures := []
  let root := testKey .ed25519 "99e87b0e9158531eeeb503ff15266e2b23c2a2507b138c9d1b1f2ab458df2d61"
  let ephemeral := testKey .ed25519
    "1111111111111111111111111111111111111111111111111111111111111111"
  let .ok rootPublic := root.publicKey | pure ["could not derive the root public key"]
  let .ok authority := BlockBuilder.code {}
    "parent(\"a\", \"b\");\nparent(\"b\", \"c\");\nparent(\"c\", \"d\");"
    | pure ["could not parse the authority block"]
  let .ok token := Biscuit.create root ephemeral authority | pure ["could not create a token"]
  let .ok token := Biscuit.ofBytes (Biscuit.toBytes token) rootPublic
    | pure ["the token did not verify"]
  -- transitive closure: a rule must be applied until nothing new appears
  let .ok builder := AuthorizerBuilder.code {}
    ("ancestor($a, $b) <- parent($a, $b);\n"
      ++ "ancestor($a, $c) <- ancestor($a, $b), parent($b, $c);\n"
      ++ "allow if ancestor(\"a\", \"d\");")
    | pure ["could not parse the authorizer"]
  fs := expectEq fs "rules are applied to a fixpoint"
    (Authorizer.authorizeToken builder token) (.ok 0)
  -- a query reads facts back out of the world
  let .ok authorizer := Authorizer.build builder token | pure ["could not build the authorizer"]
  let (_, authorizer) := Authorizer.authorizeWithState authorizer
  let .ok query := Parser.parseAuthorizer "descendants($b) <- ancestor(\"a\", $b);"
    | pure ["could not parse the query"]
  match query.rules with
  | [q] =>
    match Authorizer.query authorizer q with
    | .error _ => fs := fs ++ ["the query failed"]
    | .ok results =>
      fs := expectEq fs "the query returns every descendant" results
        ["descendants(\"b\")", "descendants(\"c\")", "descendants(\"d\")"]
  | _ => fs := fs ++ ["the query did not parse as a single rule"]
  -- a deny policy wins over a later allow
  let .ok denying := AuthorizerBuilder.code {}
    "deny if parent(\"a\", \"b\");\nallow if true;" | pure ["could not parse the authorizer"]
  fs := expect fs "a deny policy denies"
    (Authorizer.authorizeToken denying token |>.toOption.isNone)
  pure fs

/-- Run every check in this file. -/
def runRoundTrip (samplesDir : System.FilePath) : IO Failures := do
  let mut fs : Failures := cryptoTests ++ parserTests ++ tokenTests ++ engineTests
  fs := fs ++ (← encodingTests samplesDir)
  pure fs

end LeanBiscuit.Tests
