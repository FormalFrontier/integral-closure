# API guide and historical descent reference

The [library overview](../README.md) describes the current headline results.
Import `IntegralClosure` for the public root, or use the individual source entry
points below. The [native descent reference](API.md) is a historical snapshot,
not an exhaustive reference for the current library.

## Current source entry points

| Module | Contents |
| --- | --- |
| [`IntegralClosure.RingHom`](../IntegralClosure/RingHom.lean) | Relative integrality, natural-power criteria and unit descent along homomorphisms. |
| [`IntegralClosure.Subalgebra`](../IntegralClosure/Subalgebra.lean) | Finite scalar restriction from powers of algebra generators over commutative semirings. |
| [`IntegralClosure.Polynomial`](../IntegralClosure/Polynomial.lean) | Power substitution, reciprocal evaluation and monic relations at units. |
| [`IntegralClosure.Jacobson`](../IntegralClosure/Jacobson.lean) | Jacobson radicals under integral homomorphisms of commutative rings; see the [overview](../README.md#jacobson-radicals-under-integral-homomorphisms). |
| [`IntegralClosure.LinearRetract`](../IntegralClosure/LinearRetract.lean) | Integral closedness descends along a linear retraction. |
| [`IntegralClosure.TensorProduct`](../IntegralClosure/TensorProduct.lean) | Domain and integral-closedness descent from an arbitrary field scalar extension. |

## Relative integrality and power criteria

Let `R : Type u` and `S : Type v` have structures `[CommRing R]` and `[Ring S]`,
with independent universes, and let `f : R →+* S`. These results use mathlib's
existing predicate `f.IsIntegralElem x`: there is a monic `p : R[X]` whose
evaluation `p.eval₂ f x` is zero. The assertion `f.IsIntegral` means this holds
for every `x : S`. The target ring need not be commutative, and no `Algebra R S`
structure or centrality of the coefficient images is assumed. Neither ring is
required to be a domain, nontrivial or finite.

Import `IntegralClosure.RingHom`, or the root `IntegralClosure`.

| Declaration | Arguments and conclusion |
| --- | --- |
| [`RingHom.IsIntegralElem.pow`](../IntegralClosure/RingHom.lean) | Given `hx : f.IsIntegralElem x` and any `n : ℕ`, `hx.pow n` proves `f.IsIntegralElem (x ^ n)`. This includes `n = 0`. |
| [`RingHom.IsIntegralElem.of_pow`](../IntegralClosure/RingHom.lean) | Given `hn : 0 < n` and `hx : f.IsIntegralElem (x ^ n)`, `RingHom.IsIntegralElem.of_pow hn hx` proves `f.IsIntegralElem x`. |
| [`RingHom.IsIntegralElem.pow_iff`](../IntegralClosure/RingHom.lean) | Given `hn : 0 < n`, `RingHom.IsIntegralElem.pow_iff hn` states `f.IsIntegralElem (x ^ n) ↔ f.IsIntegralElem x`; it is a simp lemma. |
| [`RingHom.isIntegral_of_forall_pow_mem_range`](../IntegralClosure/RingHom.lean) | Given `hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f`, `RingHom.isIntegral_of_forall_pow_mem_range f hf` proves `f.IsIntegral`. |

Only preservation by powers permits exponent zero; reflection and the equivalence
require a positive exponent. In the range criterion the exponent can depend on
`x`; no common exponent or surjectivity is required. The conclusion is an
integral homomorphism, not a finite extension or a `Module.Finite` assertion.
These criteria do not assert general closure under addition, multiplication or
inverses in the noncommutative target.

Power preservation reuses mathlib's `IsIntegral.pow` for the distinguished root in
the commutative ring `AdjoinRoot p`. Polynomial divisibility then transfers the
monic relation back to `S`, using power substitution and left-multiple vanishing.
Positive-power reflection uses `Polynomial.expand`; the range criterion uses a
monic relation of the form `X ^ n - C r` when `x ^ n = f r`.

## Finiteness over power-containing subalgebras

Let `R` and `A` be commutative semirings in independent universes, with the given
`Algebra R A`, and let `C : Subalgebra R A`. For a finite set `s : Finset A`,
[`Subalgebra.finite_of_adjoin_eq_top_of_forall_exists_pow_mem`](../IntegralClosure/Subalgebra.lean)
assumes `Algebra.adjoin R (s : Set A) = ⊤` and
`∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ C`. It proves `Module.Finite C A` for
the **original** `A` with the canonical inclusion action of `C`. No separate
finite-type premise is needed: the given finite generators already supply it.
Import `IntegralClosure.Subalgebra` or the root.

The all-elements corollary
[`Subalgebra.finite_of_forall_exists_pow_mem`](../IntegralClosure/Subalgebra.lean)
requires `Algebra.FiniteType R A` and a positive power of **every** `a : A` in
`C`. In either form exponents may vary with the element. No field, Noetherianity,
ring structure, finite type of `C/R`, or uniform exponent is required.

The generator-only hypothesis is genuinely weaker: `ℕ[X²] ⊊ ℕ[X]` contains
`X²`, and `1,X` span over `ℕ[X²]`. Yet no positive power of `1+X` belongs to
`ℕ[X²]`, since its `X`-coefficient is the positive natural exponent. In general
the bounded monomials span; no linear independence or basis is asserted.

The proof bounds singleton-adjoin powers by division with remainder, then uses
mathlib's `Algebra.adjoin_eq_span`, `Algebra.adjoin_union_coe_submodule` and
`Submodule.FG.mul` to multiply the resulting spans. This is a **submodule
product**, not a submodule sup or a Cartesian product. No subtraction or
integrality criterion is used; the raw ring-homomorphism criterion above is a
separate API.

## Unit relations under raw polynomial evaluation

For semirings `R`, `S` in independent universes and `f : R →+* S`, evaluation
uses coefficients on the left; their images need not be central in `S`.
For a given unit `a : Sˣ`,
[`IntegralClosure.Polynomial`](../IntegralClosure/Polynomial.lean) provides:

- `exists_monic_eval₂_units_inv_eq_zero_of_isUnit_reverse_leadingCoeff`:
  a relation `p.eval₂ f (a : S) = 0` yields a monic relation at `a⁻¹` when
  `p.reverse.leadingCoeff` is a unit **in `R`**. No `p ≠ 0` hypothesis is needed.
- `exists_monic_eval₂_units_inv_eq_zero`: if `R` is a division semiring,
  a nonzero polynomial relation at `a` yields a monic relation at `a⁻¹`.
- `exists_monic_eval₂_units_eq_zero_and_inv_iff`: monic relations at both
  `a` and `a⁻¹` exist exactly when there is a monic relation at `a` whose
  constant coefficient is a unit in `R`, not merely after applying `f`.
  `exists_monic_coeff_zero_eq_one_eval₂_units_eq_zero` chooses that coefficient
  to be `1` when both relations exist.

The separate
[`RingHom.isUnit_of_monic_eval₂_units_inv_eq_zero`](../IntegralClosure/RingHom.lean)
assumes `f` injective, `r : R`, and `↑a = f r`. A monic relation at `a⁻¹`
then implies `IsUnit r`; no second relation at `a` or commutativity is required.
Although stated with semiring instances, these hypotheses force both semirings
to admit ring structures. This is not unit reflection from injectivity alone.
The proof refines mathlib's `RingHom.IsIntegral.isLocalHom` reverse-polynomial
argument and uses Group Theory's zero-sum unit-transfer API.

## Polynomial evaluation helpers

Import `IntegralClosure.Polynomial` directly for these helpers; it is also publicly
imported by `IntegralClosure.RingHom`. The universes of the coefficient and target
types are independent. None of these identities requires the coefficient images
to be central in the target.

| Declaration | Assumptions and identity |
| --- | --- |
| [`Polynomial.eval₂_comp_X_pow`](../IntegralClosure/Polynomial.lean) | For `[Semiring R]`, `[Semiring S]`, `f : R →+* S`, `x : S`, `n : ℕ` and `p : R[X]`, `eval₂ f x (p.comp (X ^ n)) = eval₂ f (x ^ n) p`. |
| [`Polynomial.eval₂_expand`](../IntegralClosure/Polynomial.lean) | For `[CommSemiring R]` and `[Semiring S]`, `eval₂ f x (expand R n p) = eval₂ f (x ^ n) p`. This is a simp lemma and permits every natural `n`. |
| [`Polynomial.eval₂_mul_eq_zero_of_right'`](../IntegralClosure/Polynomial.lean) | For `[Semiring R]` and `[Semiring S]`, if `hq : q.eval₂ f x = 0`, then `Polynomial.eval₂_mul_eq_zero_of_right' f x p hq` proves `(p * q).eval₂ f x = 0`. The vanishing polynomial `q` is the **right** factor. |

The last identity says that every **left multiple** of a vanishing polynomial
vanishes. It is not a general multiplicativity theorem for `eval₂ f x`. The
substitution identities concern powers of `X`, not arbitrary polynomial
composition in a noncommutative target.

## Historical native snapshot

`API.md` retains the native displayed signatures and original project docstrings
for the five descent/evaluation declarations in `LinearRetract` and `TensorProduct`,
the aggregate root, and four private test/example modules. Its recorded analysis
revision is `ae76530b1ba4d38d1dafef90a68f2fb0cce64157`.

The unchanged [generation manifest](api-manifest.json) records that historical
analysis: ten source/pin hashes, seven native-record hashes, the old module/public
inventories, the tool revision and the original output hash. Those input/output
bindings do **not** bind this edited guide or the edited `API.md` introduction,
and do not cover the current `Jacobson`, `RingHom`, `Subalgebra` or `Polynomial`
modules. The manual sections above are separate from the retained native snapshot.

The reference is not an interactive dependency website and bundles no JavaScript,
fonts, remote styles, mathematical source PDF or external documentation text.
Source hyperlinks resolve relatively to the files in this checkout.

### Optional historical reproduction

To reproduce the original snapshot, use its analyzed sources and configuration,
not the current tree's additional modules or edited documentation wrappers. The
following recipe describes the historical seven-module generation only.

When the analyzed development commit is available locally, the historical adapter
compares the source/pin inputs with its Git objects. This path does not enforce the
committed manifest or the original native-record/output hashes. If that full commit
object is absent, the fallback requires the working manifest to equal its committed
version and the reproduced manifest to match it byte-for-byte, including source/pin
and native-record hashes, inventories, tool revision and output hash; source inputs
must also match the checkout's committed files. A present non-commit object or
source/pin drift is refused. An uncommitted manifest or changed native-record hashes
are also refused in the missing-commit fallback.

In either path, `--check` compares regenerated Markdown and manifest bytes with the
working-tree files. With the analyzed commit present, regenerating both files from
structurally valid changed native records can therefore pass a subsequent `--check`;
it does not independently enforce the original committed native-record/output hashes.
These checks bind source/output bytes, not native-run or proof attestation, and do
not assert that the old analyzed revision is available at GitHub. The manifest's
`proof_certification: false` does not assert any proof or axiom verification.

Build the unchanged native doc-gen4 tool at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed dependency manifest
and Lean `v4.34.0-rc2`, in a separate checkout using `lake build doc-gen4`.
This core-only tool must not change this library's mathematical dependencies.
Fetch the historical sources' matching mathlib cache and build their seven modules,
using the build commands described in the root README.

Use the following native commands in that historical pinned Lake environment.
Replace the absolute tool/output paths and `FULL_SOURCE_COMMIT` with the recorded
full analyzed source revision, not a moving branch. Use a new database/output
directory for each generation. Create both chosen output directories before the
native commands: the SQLite opener does not create its parent directory. Repeat
`single` for each of the seven modules listed in the historical
`scripts/generate_api.py`, using its matching path in the source URI:

```sh
mkdir /tmp/integral-analysis /tmp/integral-render
lake env /path/to/doc-gen4 single --build /tmp/integral-analysis IntegralClosure.LinearRetract api.db https://github.com/FormalFrontier/integral-closure/blob/FULL_SOURCE_COMMIT/IntegralClosure/LinearRetract.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/integral-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/integral-render --manifest /tmp/integral-render/manifest.json /tmp/integral-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/integral-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/integral-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

The native renderer's intermediate HTML, scripts/assets and dependency pages are
not bundled with the Markdown reference and manifest. A source URI is an immutable
analysis identifier, not proof that an unpublished development commit is remotely
available at that GitHub URL.

### Scope of the historical adapter

The bounded adapter expects the historical seven module records and exactly five
public names/kinds/origins. Its checks reject source/pin drift, missing docstrings,
malformed header markup and missing essential assumptions. It retains every native
header text token, normalizing whitespace only. Module comments are extracted
from the analyzed sources' simple, single module-doc block per source. The adapter
is not a general Lean parser, native-output attestation or proof checker; these
checks do not describe the current library's full public API.

## Provenance

The adapter adapts the original Formal Frontier ideal-completion renderer recipe.
The original renderer and this adaptation are distinct contributions by Formal
Frontier agents, including AI agents. Collective credit and Apache-2.0 terms are
preserved. Original library docstrings and generated mathematical signatures
are covered by the library's provenance record. Lean, mathlib and doc-gen4 remain
separately credited declared tools/dependencies; their implementation or external
documentation is not copied into this reference.
