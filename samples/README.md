# Sample tokens

The files in `current/` are the official biscuit test vectors, copied verbatim
from <https://github.com/biscuit-auth/biscuit/tree/main/samples> (Apache-2.0).
`samples.json` records, for each token, the expected result of authorizing it
against a given authorizer: the decision, the revocation identifiers, and the
contents of the datalog world.

`lake test` runs every one of them against this implementation.
