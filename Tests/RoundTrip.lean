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

/-- Bytes from hex, empty if malformed. -/
def hexBytes (s : String) : Bytes := (Bytes.ofHex? s).getD Bytes.empty

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

/-! ## Signing outside the library -/

/-- What the old implementation (commit 669c5c8, before the `…With` forms)
produced for fixed keys, in hex: an Ed25519-rooted token, the same with a block
appended under a secp256r1 next key, a secp256r1 third party's block for it,
the token with that block appended, and a secp256r1-rooted token with and
without an appended block.  Both signature schemes are deterministic here
(RFC 8032, RFC 6979), so the bytes are fixed. -/
def golden : List (String × String) := [
  ("edCreate",
    "12b9010a4f0a05616c696365180422090a07080a120318800832120a100a02081b1206080f120218"
    ++ "0d220210004225080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e970cd76830"
    ++ "35f25e7d122408001220d04ab232742bb4ab3a1368bd4615e4e6d0224ab71a016baf8520a332c977"
    ++ "87371a406cb374e1eb6793ec9e80a24a65a885314bda9686072a61e9e000b19064d10f3d5871aeb4"
    ++ "9b9b74a4f9d4295999c2dfc6f3587155e34a236014e399ef348e550c22220a201111111111111111"
    ++ "111111111111111111111111111111111111111111111111"),
  ("edAppendP256Next",
    "12b9010a4f0a05616c696365180422090a07080a120318800832120a100a02081b1206080f120218"
    ++ "0d220210004225080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e970cd76830"
    ++ "35f25e7d122408001220d04ab232742bb4ab3a1368bd4615e4e6d0224ab71a016baf8520a332c977"
    ++ "87371a406cb374e1eb6793ec9e80a24a65a885314bda9686072a61e9e000b19064d10f3d5871aeb4"
    ++ "9b9b74a4f9d4295999c2dfc6f3587155e34a236014e399ef348e550c1a7f0a121803320e0a0c0a02"
    ++ "081b1206080312021800122508011221025b36890dacbd7c9a96bb74a1ee28b3d2d75b72e09a20ef"
    ++ "25cf8e6fd8a9f0350d1a40f213b3363917662720c43d17782bd41ec02b634970e60d509e8f244b08"
    ++ "69a4e5a87145e0c2ae50d167bc611354ef544b2193f58130b9e3c1a7774d4fbca49d0d280122220a"
    ++ "204444444444444444444444444444444444444444444444444444444444444444"),
  ("thirdParty",
    "0a0c180522080a06080f1202180d12700a473045022100cbfe2b7a5bd0c8a256162e624eeaca3d4f"
    ++ "fde2d7fd0c8bddbd1d26a74c9513bf02203da1e83972755b328097c5214d5932ebd125f14990a936"
    ++ "3dc7b720284aa3f08d1225080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e97"
    ++ "0cd7683035f25e7d"),
  ("edWithThirdParty",
    "12b9010a4f0a05616c696365180422090a07080a120318800832120a100a02081b1206080f120218"
    ++ "0d220210004225080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e970cd76830"
    ++ "35f25e7d122408001220d04ab232742bb4ab3a1368bd4615e4e6d0224ab71a016baf8520a332c977"
    ++ "87371a406cb374e1eb6793ec9e80a24a65a885314bda9686072a61e9e000b19064d10f3d5871aeb4"
    ++ "9b9b74a4f9d4295999c2dfc6f3587155e34a236014e399ef348e550c1a7f0a121803320e0a0c0a02"
    ++ "081b1206080312021800122508011221025b36890dacbd7c9a96bb74a1ee28b3d2d75b72e09a20ef"
    ++ "25cf8e6fd8a9f0350d1a40f213b3363917662720c43d17782bd41ec02b634970e60d509e8f244b08"
    ++ "69a4e5a87145e0c2ae50d167bc611354ef544b2193f58130b9e3c1a7774d4fbca49d0d28011af001"
    ++ "0a0c180522080a06080f1202180d122408001220a09aa5f47a6759802ff955f8dc2d2a14a5c99d23"
    ++ "be97f864127ff9383455a4f01a46304402207b523f6eda04498041b717c3c69b5e89b6e771bbfc1f"
    ++ "d59ba4499bd54f57bfab022004f4167f731ce5b842b87056dc25cddfffeeb759dc84b73a2b6e6406"
    ++ "418d89ab22700a473045022100cbfe2b7a5bd0c8a256162e624eeaca3d4ffde2d7fd0c8bddbd1d26"
    ++ "a74c9513bf02203da1e83972755b328097c5214d5932ebd125f14990a9363dc7b720284aa3f08d12"
    ++ "25080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e970cd7683035f25e7d2801"
    ++ "22220a202222222222222222222222222222222222222222222222222222222222222222"),
  ("p256Create",
    "12c2010a4f0a05616c696365180422090a07080a120318800832120a100a02081b1206080f120218"
    ++ "0d220210004225080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e970cd76830"
    ++ "35f25e7d1225080112210257e977f6db7e33c3fe7acf2842ed987009caf56d458682fca447b7d3d7"
    ++ "62ab341a46304402204719e2ae7ed85b5e1b631d6328b6e4c96b650288ff636c6d61a3ded8fd6a6c"
    ++ "ab0220572b860cd9acce7cfb1f573a11d3c830104115a98a3597c6dd0ee566eb49f4cd280122220a"
    ++ "205555555555555555555555555555555555555555555555555555555555555555"),
  ("p256Append",
    "12c2010a4f0a05616c696365180422090a07080a120318800832120a100a02081b1206080f120218"
    ++ "0d220210004225080112210351a7580833898ea1b183cbd7350a4099078c6ef1c1e18e970cd76830"
    ++ "35f25e7d1225080112210257e977f6db7e33c3fe7acf2842ed987009caf56d458682fca447b7d3d7"
    ++ "62ab341a46304402204719e2ae7ed85b5e1b631d6328b6e4c96b650288ff636c6d61a3ded8fd6a6c"
    ++ "ab0220572b860cd9acce7cfb1f573a11d3c830104115a98a3597c6dd0ee566eb49f4cd28011a8501"
    ++ "0a121803320e0a0c0a02081b1206080312021800122408001220d04ab232742bb4ab3a1368bd4615"
    ++ "e4e6d0224ab71a016baf8520a332c97787371a47304502210089a931d4ad95b196b96e8ace134187"
    ++ "86916bcb9a4627ab9909e8cc1e5d4e1b970220495b86e629a7740dec6ff3e09561359790ec80a658"
    ++ "d11bea2ba2b0090696ad26280122220a201111111111111111111111111111111111111111111111"
    ++ "111111111111111111")]

/-- The golden hex of a name. -/
def goldenHex (name : String) : String := ((golden.find? (·.1 == name)).map (·.2)).getD ""

/-- The signer the tests stand in for an external one with: it records every
payload it is asked to sign and signs with the primitives directly, not through
`PrivateKey`.  A signing failure is an error of the signer's own monad. -/
abbrev SignerM := EStateM String (List Bytes)

/-- Sign as `recordingSigner` does with key `k`. -/
def recordingSigner (k : PrivateKey) (payload : Bytes) : SignerM Bytes := do
  modify (· ++ [payload])
  let signature := match k.algorithm with
    | .ed25519 => Ed25519.sign k.key payload
    | .secp256r1 => P256.sign k.key payload
  match signature with
  | some s => pure s
  | none => throw "the test signer could not sign"

/-- A signer that records the payload and answers with a fixed signature. -/
def fixedSigner (signature : Bytes) (payload : Bytes) : SignerM Bytes := do
  modify (· ++ [payload])
  pure signature

/-- Run a computation against a test signer: its outcome — `none` if the signer
itself failed — and the payloads it was asked to sign. -/
def recording (x : ExceptT TokenError SignerM α) : Option (Except TokenError α) × List Bytes :=
  match x.run.run [] with
  | .ok r s => (some r, s)
  | .error _ s => (none, s)

/-- Whether a recorded outcome is a token error. -/
def refused : Option (Except TokenError α) → Bool
  | some (.error _) => true
  | _ => false

/-- The hex of a recorded token, or empty. -/
def recordedHex : Option (Except TokenError Token.Biscuit) → String
  | some (.ok t) => Bytes.toHex t.toBytes
  | _ => ""

/-- A secp256r1 DER signature as the raw `r ‖ s` JWS uses, which a token must
not carry. -/
def rawRS (der : Bytes) : Bytes :=
  match P256.Der.parseSignature der with
  | some (r, s) => Bytes.ofNatBE 32 r ++ Bytes.ofNatBE 32 s
  | none => Bytes.empty

/-- The `…With` forms against a signer the library does not hold.  The plain
forms still produce the bytes the old implementation produced, the `…With`
forms produce the same bytes with a correct signer, and every signature a
signer returns that does not verify under the declared key — another key's,
empty, the wrong length, raw `r ‖ s` instead of DER — is refused. -/
def externalSignerTests : Failures := Id.run do
  let mut fs : Failures := []
  let rootEd := testKey .ed25519 "99e87b0e9158531eeeb503ff15266e2b23c2a2507b138c9d1b1f2ab458df2d61"
  let rootP := testKey .secp256r1
    "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"
  let next1 := testKey .ed25519 "1111111111111111111111111111111111111111111111111111111111111111"
  let next2 := testKey .ed25519 "2222222222222222222222222222222222222222222222222222222222222222"
  let nextP := testKey .secp256r1
    "4444444444444444444444444444444444444444444444444444444444444444"
  let nextP2 := testKey .secp256r1
    "5555555555555555555555555555555555555555555555555555555555555555"
  let third := testKey .secp256r1
    "3333333333333333333333333333333333333333333333333333333333333333"
  let stranger := testKey .ed25519
    "6666666666666666666666666666666666666666666666666666666666666666"
  let strangerP := testKey .secp256r1
    "7777777777777777777777777777777777777777777777777777777777777777"
  let .ok rootEdPublic := rootEd.publicKey | pure ["could not derive a public key"]
  let .ok rootPPublic := rootP.publicKey | pure ["could not derive a public key"]
  let .ok thirdPublic := third.publicKey | pure ["could not derive a public key"]
  let .ok auth := BlockBuilder.code {}
    s!"user(\"alice\");\ncheck if group(\"admin\") trusting {thirdPublic.print};"
    | pure ["could not parse the authority block"]
  let .ok restriction := BlockBuilder.code {} "check if operation(\"read\");"
    | pure ["could not parse the attenuating block"]
  let .ok thirdBlock := BlockBuilder.code {} "group(\"admin\");"
    | pure ["could not parse the third-party block"]
  let authorize (t : Token.Biscuit) (code : String) : Except TokenError Nat := do
    Authorizer.authorizeToken (← AuthorizerBuilder.code {} code) t
  -- The plain forms against the old implementation's bytes.
  let .ok a0 := Biscuit.create rootEd next1 auth | pure ["create failed"]
  fs := expectEq fs "create gives the old bytes" (Bytes.toHex a0.toBytes) (goldenHex "edCreate")
  let .ok a1 := a0.append nextP restriction | pure ["append failed"]
  fs := expectEq fs "append under a secp256r1 next key gives the old bytes"
    (Bytes.toHex a1.toBytes) (goldenHex "edAppendP256Next")
  let request := a1.thirdPartyRequest
  let .ok contents := Biscuit.signThirdPartyBlock third request thirdBlock
    | pure ["signThirdPartyBlock failed"]
  fs := expectEq fs "signThirdPartyBlock gives the old bytes"
    (Bytes.toHex (Schema.encodeThirdPartyBlockContents contents)) (goldenHex "thirdParty")
  let .ok a2 := a1.appendThirdParty next2 contents | pure ["appendThirdParty failed"]
  fs := expectEq fs "appendThirdParty gives the old bytes" (Bytes.toHex a2.toBytes)
    (goldenHex "edWithThirdParty")
  let .ok b0 := Biscuit.create rootP nextP2 auth | pure ["create failed"]
  fs := expectEq fs "a secp256r1 root gives the old bytes" (Bytes.toHex b0.toBytes)
    (goldenHex "p256Create")
  let .ok b1 := b0.append next1 restriction | pure ["append failed"]
  fs := expectEq fs "and so does appending to it" (Bytes.toHex b1.toBytes)
    (goldenHex "p256Append")
  -- The `…With` forms with a correct signer: the same bytes, one signature each.
  let (w0, ps) := recording (Biscuit.createWith rootEdPublic (recordingSigner rootEd) next1 auth)
  fs := expectEq fs "createWith gives the old bytes" (recordedHex w0) (goldenHex "edCreate")
  fs := expectEq fs "createWith asks for one signature" ps.length 1
  let .ok proof0 := a0.proofKey | pure ["no proof key"]
  let .ok proof0Public := proof0.publicKey | pure ["no proof public key"]
  let (w1, ps) := recording (a0.appendWith proof0Public (recordingSigner proof0) nextP restriction)
  fs := expectEq fs "appendWith gives the old bytes" (recordedHex w1)
    (goldenHex "edAppendP256Next")
  fs := expectEq fs "appendWith asks for one signature" ps.length 1
  let (c, ps) := recording (Biscuit.signThirdPartyBlockWith thirdPublic (recordingSigner third)
    request thirdBlock)
  fs := expectEq fs "signThirdPartyBlockWith gives the old bytes"
    (match c with
     | some (.ok c) => Bytes.toHex (Schema.encodeThirdPartyBlockContents c)
     | _ => "") (goldenHex "thirdParty")
  fs := expectEq fs "signThirdPartyBlockWith asks for one signature" ps.length 1
  let .ok proof1 := a1.proofKey | pure ["no proof key"]
  let .ok proof1Public := proof1.publicKey | pure ["no proof public key"]
  let (w2, _) := recording
    (a1.appendThirdPartyWith proof1Public (recordingSigner proof1) next2 contents)
  fs := expectEq fs "appendThirdPartyWith gives the old bytes" (recordedHex w2)
    (goldenHex "edWithThirdParty")
  let (wb, _) := recording (Biscuit.createWith rootPPublic (recordingSigner rootP) nextP2 auth)
  fs := expectEq fs "createWith with a secp256r1 root gives the old bytes" (recordedHex wb)
    (goldenHex "p256Create")
  match w2 with
  | some (.ok t) =>
    match Biscuit.ofBytes t.toBytes rootEdPublic with
    | .ok t =>
      fs := expectEq fs "the externally signed token authorizes"
        (authorize t "operation(\"read\");\nallow if user(\"alice\");") (.ok 0)
      fs := expect fs "and its attenuation binds"
        (authorize t "operation(\"write\");\nallow if true;" |>.toOption.isNone)
    | .error _ => fs := fs ++ ["the externally signed token did not verify"]
  | _ => fs := fs ++ ["appendThirdPartyWith failed"]
  -- A signer holding another key than the one declared is refused after signing.
  let (r, ps) := recording (Biscuit.createWith rootEdPublic (recordingSigner stranger) next1 auth)
  fs := expect fs "createWith refuses a signer for another key" (refused r && ps.length == 1)
  let (r, _) := recording (Biscuit.createWith rootPPublic (recordingSigner strangerP) nextP2 auth)
  fs := expect fs "also for secp256r1" (refused r)
  let (r, _) := recording (a0.appendWith proof0Public (recordingSigner stranger) nextP restriction)
  fs := expect fs "appendWith refuses a signer for another key" (refused r)
  let (r, _) := recording
    (Biscuit.signThirdPartyBlockWith thirdPublic (recordingSigner strangerP) request thirdBlock)
  fs := expect fs "signThirdPartyBlockWith refuses a signer for another key" (refused r)
  -- A declared key that is not the token's last is refused before signing.
  let (r, ps) := recording (a0.appendWith rootEdPublic (recordingSigner rootEd) nextP restriction)
  fs := expect fs "appendWith refuses a declared key the token does not name, unsigned"
    (refused r && ps.isEmpty)
  -- Malformed signatures.
  let edSig := (Ed25519.sign rootEd.key (hexBytes "00")).getD Bytes.empty
  let pDer := (P256.sign rootP.key (hexBytes "00")).getD Bytes.empty
  let malformed : List (String × Bytes) := [("empty", Bytes.empty),
    ("63 bytes", edSig.extract 0 63), ("65 bytes", edSig ++ hexBytes "00"),
    ("garbage", Bytes.ofString "not a signature at all, not at all, not at all, not at all!!")]
  for (what, sig) in malformed do
    let (r, _) := recording (Biscuit.createWith rootEdPublic (fixedSigner sig) next1 auth)
    fs := expect fs s!"createWith refuses a signature that is {what}" (refused r)
    let (r, _) := recording (a0.appendWith proof0Public (fixedSigner sig) nextP restriction)
    fs := expect fs s!"appendWith refuses a signature that is {what}" (refused r)
    let (r, _) := recording
      (Biscuit.signThirdPartyBlockWith thirdPublic (fixedSigner sig) request thirdBlock)
    fs := expect fs s!"signThirdPartyBlockWith refuses a signature that is {what}" (refused r)
  -- Raw r ‖ s instead of DER, from the right key.
  let rawSigner (k : PrivateKey) (payload : Bytes) : SignerM Bytes := do
    pure (rawRS (← recordingSigner k payload))
  let (r, _) := recording (Biscuit.createWith rootPPublic (rawSigner rootP) nextP2 auth)
  fs := expect fs "createWith refuses raw r ‖ s for secp256r1" (refused r)
  let .ok proofB := b0.proofKey | pure ["no proof key"]
  let .ok proofBPublic := proofB.publicKey | pure ["no proof public key"]
  fs := expect fs "the secp256r1 token's proof key is secp256r1"
    (proofBPublic.algorithm == .secp256r1)
  let (r, _) := recording (b0.appendWith proofBPublic (rawSigner proofB) next1 restriction)
  fs := expect fs "appendWith refuses raw r ‖ s for secp256r1" (refused r)
  let (r, _) := recording
    (Biscuit.signThirdPartyBlockWith thirdPublic (rawSigner third) request thirdBlock)
  fs := expect fs "signThirdPartyBlockWith refuses raw r ‖ s" (refused r)
  fs := expect fs "the raw form is the right length, so only its encoding is wrong"
    ((rawRS pDer).size == 64)
  -- A signer that fails is the signer's own error, and no token.
  let failing (_ : Bytes) : SignerM Bytes := throw "the hardware module is unplugged"
  let (r, _) := recording (Biscuit.createWith rootEdPublic failing next1 auth)
  fs := expect fs "a failing signer gives no token" r.isNone
  -- Sealed tokens take no block, however it would be signed.
  let .ok sealed := Biscuit.sealToken a0 | pure ["could not seal"]
  let (r, ps) := recording
    (sealed.appendWith proof0Public (recordingSigner proof0) nextP restriction)
  fs := expect fs "appendWith refuses a sealed token, unsigned"
    ((match r with
      | some (.error .appendOnSealed) => true
      | _ => false) && ps.isEmpty)
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
  let mut fs : Failures := cryptoTests ++ parserTests ++ tokenTests ++ externalSignerTests ++
    engineTests
  fs := fs ++ (← encodingTests samplesDir)
  pure fs

end LeanBiscuit.Tests
