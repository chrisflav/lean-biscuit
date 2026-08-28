# lean-biscuit

An implementation of the [Biscuit](https://doc.biscuitsec.org) authorization
token in Lean 4, written against the
[specification](https://doc.biscuitsec.org/reference/specifications.html) and
checked against its official test vectors.

Biscuit is a bearer token that can be *attenuated offline*: whoever holds a
token can derive a strictly less powerful one without talking to the issuer, and
anyone who knows the root public key can verify the result. What a token allows
is described in a small Datalog dialect, so the authorization decision is a
logic query rather than an ad-hoc check.

## What is implemented

The whole specification, with no external dependencies — the cryptography, the
wire format and the logic engine are all written here:

- **Cryptography**: SHA-256, SHA-512, HMAC-SHA256, Ed25519 (RFC 8032) signing
  and strict verification, and ECDSA over secp256r1 with deterministic nonces
  (RFC 6979), including SEC1 DER signatures and compressed point encodings.
- **Wire format**: a Protocol Buffers reader and writer, and the biscuit
  container: the signature chain, third-party signatures, sealed tokens, and
  the symbol and public key tables.
- **Datalog**: terms (integers, strings, dates, byte strings, booleans, null,
  sets, arrays and maps), the full expression opcode set with closures and
  short-circuiting operators, external function calls, rules, the three
  flavours of check, and allow/deny policies. Facts carry origins, so a rule
  only ever sees the blocks its scope trusts.
- **Text format**: a parser and a printer for Datalog source, matching the
  grammar and the rendering of the reference implementation.
- **Tokens**: creating, attenuating, sealing, third-party blocks, verification
  against a root key (or a key chosen by the token's `rootKeyId`), unverified
  inspection, authorization, and queries over an authorized token.

## Building and testing

```sh
lake build      # build the library and the command line tool
lake test       # run the specification's sample tokens, plus round-trip tests
```

`lake test` runs every token in `samples/` — the official test vectors — and
compares the decision, the revocation identifiers and the *entire* contents of
the Datalog world against what the specification records, down to the rendering
of each fact, rule and check. It then creates, attenuates, seals and re-reads
tokens of its own, checks that every sample block re-encodes to its original
bytes, and pins the cryptographic primitives to published test vectors.

## Command line

```sh
lean-biscuit inspect   <token> [--base64]
lean-biscuit verify    <token> <root-public-key> [--base64]
lean-biscuit authorize <token> <root-public-key> <authorizer.datalog> [--base64]
```

A root public key is written as `ed25519/<hex>` or `secp256r1/<hex>`.

```
$ lean-biscuit inspect samples/current/test024_third_party.bc
// NOTE: signatures were not verified
// authority, datalog v3.1
right("read");
check if group("admin") trusting ed25519/acdd6d5b53bfee478bf689f8e012fe7988bf755e3d7c5152947abc149bc20189;

// block 1 (signed by ed25519/acdd6d5b53bfee478bf689f8e012fe7988bf755e3d7c5152947abc149bc20189), datalog v3.2
group("admin");
check if right("read");
```

## Using it as a library

```lean
import LeanBiscuit

open LeanBiscuit LeanBiscuit.Token

def example (root : PrivateKey) (ephemeral : PrivateKey) : Except TokenError String := do
  let authority ← BlockBuilder.code {} "right(\"file1\", \"read\");"
  let token ← Biscuit.create root ephemeral authority
  pure (Biscuit.toBase64 token)
```

## Structure

| Module | Contents |
| --- | --- |
| `LeanBiscuit.Util` | bytes, hex, base64, dates, regular expressions |
| `LeanBiscuit.Crypto` | hashes, Ed25519, secp256r1, keys |
| `LeanBiscuit.Proto` | the Protocol Buffers wire format and the container |
| `LeanBiscuit.Datalog` | terms, syntax, symbol tables, evaluation, the world |
| `LeanBiscuit.Builder` | Datalog before interning, and the translation both ways |
| `LeanBiscuit.Parser` | the Datalog text format |
| `LeanBiscuit.Token` | blocks, signatures, tokens, creation, authorization |

## Design notes

The library is written with formal verification in mind, so it is arranged to
be easy to state properties about later:

- Everything outside the command line tool is pure and total: the library
  contains no `partial` definitions and no `sorry`, and does not use `IO`.
- Recursion that is not structural is bounded by something the input determines,
  and the bound is stated in the code. Protobuf messages nest no deeper than the
  byte string that holds them; an expression's closures nest no deeper than its
  own opcode count; a term in the text format nests no deeper than the source is
  long. The Datalog engine takes its iteration and fact limits as a parameter,
  and the regular expression engine is a Thompson NFA simulation that visits
  each input position once rather than a backtracker.
- Values that have a canonical form keep it: sets are sorted and deduplicated,
  maps are sorted by key, and origins are sorted sets of block ids. Structural
  equality on the representation therefore coincides with equality of the value.
- The one place where behaviour is deliberately *not* reproduced is the
  reference implementation's wall-clock timeout, which would make the result of
  an authorization depend on the speed of the machine. The fact and iteration
  limits, which depend only on the token, are enforced.

## Licence and test vectors

The files under `samples/` are the official biscuit test vectors, copied from
the specification repository under the Apache-2.0 licence.
