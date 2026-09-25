# Generated API reference

`API.md` is the release-local reference for all five public declarations, the
three production modules and four private test/example modules. It retains
native displayed signatures, including implicit assumptions, and the original
project docstrings. Source links point to the files shipped in this checkout.
The reference is not an interactive dependency website and bundles no JavaScript,
fonts, remote styles, mathematical source PDF or external documentation text.

## Reproduction

The exact analyzed Lean/configuration inputs are identified by full revision and
SHA256 in `api-manifest.json`. Final release review additionally binds this manifest
and generated file to the final candidate commit/tree. Documentation-only later
commits do not change those mathematical input hashes; source or pin changes
require fresh native generation and affected verification.

When the analyzed development commit is available locally, its Git source objects
are authoritative and every input must match. A parentless release checkout does
not contain that development ancestry. Only when the selected full commit object
is absent does the adapter instead require the release's committed manifest to
equal the freshly reproduced manifest byte-for-byte, including all ten source/pin
hashes, seven native-record hashes, module/public inventories, tool revision and
output hash. Its source inputs must also equal the release's own committed files.
A present wrong object, stale input, altered native record or uncommitted manifest
is refused. This is source/output binding, not native-run attestation or a claim
that the old development revision is available at GitHub.

Build the unchanged native doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed dependency manifest
and Lean `v4.34.0-rc2`, in a separate checkout using `lake build doc-gen4`.
This core-only tool must not change this library's mathematical dependencies.
First fetch this library's matching mathlib cache and build its seven modules,
as described in the root README.

Use the following native commands in this library's pinned Lake environment.
Replace the absolute tool/output paths and `FULL_SOURCE_COMMIT` with the actual
full analyzed source revision, not a moving branch. Use a new database/output
directory for each generation. Create both chosen output directories before the
native commands: the SQLite opener does not create its parent directory. Repeat
`single` for each of the seven modules
listed in `scripts/generate_api.py`, using its matching path in the source URI:

```sh
mkdir /tmp/integral-analysis /tmp/integral-render
lake env /path/to/doc-gen4 single --build /tmp/integral-analysis IntegralClosure.LinearRetract api.db https://github.com/FormalFrontier/integral-closure/blob/FULL_SOURCE_COMMIT/IntegralClosure/LinearRetract.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/integral-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/integral-render --manifest /tmp/integral-render/manifest.json /tmp/integral-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/integral-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/integral-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

Only the Markdown reference and its manifest are shipped, not the intermediate
HTML, scripts/assets or dependency pages. A source URI is an immutable analysis
identifier, not proof that an unpublished development commit is remotely available
at that GitHub URL. Distributed source hyperlinks instead resolve relatively.

## Scope, checks and provenance

The bounded adapter requires every module record and exactly the expected five
public names/kinds/origins. It refuses source/pin drift, missing docstrings,
malformed header markup and missing essential assumptions. It retains every native
header text token, normalizing whitespace only. Module comments are extracted
from this library's simple, single module-doc block per source. The adapter is
not a general Lean parser, native-output attestation, proof checker or release
certificate; retained native command receipts and independent review are required.

The adapter was adapted by Atlas from Anchor's original Formal Frontier
ideal-completion contribution at `f0c8c34386109116e4912fb425a8ad15d9dc42a4`.
That recipe was unreviewed when reused; no approval transfers with it. Collective
credit and Apache-2.0 terms are preserved. Original library docstrings and generated
mathematical signatures are covered by the library's provenance record. Lean,
mathlib and doc-gen4 remain separately credited declared tools/dependencies; their
implementation or external documentation is not copied into this reference.
