module

public import Crypto

/-!
# Hashes and HMAC

Ed25519 (RFC 8032) hashes with SHA-512, ECDSA over secp256r1 with SHA-256, and
its RFC 6979 nonces with HMAC-SHA256.  None of these are implemented here: they
come from `lean-crypto-hash`, which is checked against the NIST CAVP and ACVP
vectors.  This module only fixes the algorithm and returns plain byte strings,
which is what the signature code works with.

It is a `module` because `lean-crypto-hash` is built for the module system; the
rest of the library imports it as an ordinary file.
-/

public section

namespace LeanBiscuit

/-- SHA-256 (FIPS 180-4). -/
def Sha256.hash (msg : ByteArray) : ByteArray :=
  (Crypto.Hash.digest .sha256 msg).toByteArray

/-- SHA-512 (FIPS 180-4). -/
def Sha512.hash (msg : ByteArray) : ByteArray :=
  (Crypto.Hash.digest .sha512 msg).toByteArray

/-- HMAC-SHA256 (RFC 2104). -/
def Hmac.sha256 (key message : ByteArray) : ByteArray :=
  (Crypto.HMAC.compute .sha256 key message).toByteArray

end LeanBiscuit

end