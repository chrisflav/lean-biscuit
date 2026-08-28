import LeanBiscuit.Crypto.Sha256

/-!
# HMAC-SHA256 and RFC 6979

ECDSA needs a per-signature nonce that must never repeat and never be
predictable.  RFC 6979 derives it deterministically from the secret key and the
message, which removes the need for a random source and makes signing
reproducible — a useful property for a library meant to be verified.
-/

namespace LeanBiscuit
namespace Hmac

/-- The SHA-256 block size, in bytes. -/
def blockSize : Nat := 64

/-- Exclusive or of a byte string with a repeated pad byte, extended to a full
block with zeroes. -/
def padXor (key : Bytes) (pad : UInt8) : Bytes :=
  Bytes.ofList ((List.range blockSize).map fun i =>
    (if i < key.size then key[i]! else 0) ^^^ pad)

/-- HMAC-SHA256. -/
def sha256 (key message : Bytes) : Bytes :=
  let key := if key.size > blockSize then Sha256.hash key else key
  let inner := Sha256.hash (padXor key 0x36 ++ message)
  Sha256.hash (padXor key 0x5c ++ inner)

end Hmac
end LeanBiscuit
