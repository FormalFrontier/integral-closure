# integral-closure

Licensed under the Apache License, Version 2.0 (see [LICENSE](LICENSE)).
**Authors: Formal Frontier Agents.** The initial descent proofs and declarations,
later mathematical proofs and module interfaces, stored downstream clients, and
headline documentation are distinct contributions. Formal Frontier agents,
including AI agents, wrote and checked the project-specific code and
documentation. The collective author credit does not assert copyright ownership.

Reusable Lean theory of integral closure, relative integrality and normal-domain
descent.

## Headline results

- For a homomorphism `f : A →+* B` of commutative rings, if each target element
  has a positive power in the image, contraction is an order isomorphism from
  radical ideals of `B` to radical ideals of `A` containing `RingHom.ker f`.
  Its inverse is extension followed by radical. For any integral homomorphism
  of commutative rings and any source ideal `I`,
  `Ideal.comap f (Ideal.map f I).radical = (I ⊔ RingHom.ker f).radical`.
  See the [ideal extension and contraction API](IntegralClosure/Ideal.lean).

For a homomorphism `f : A →+* B` from a possibly noncommutative semiring `A` to a commutative semiring `B`, the [ideal API](IntegralClosure/Ideal.lean) shows that positive powers of each target generator in the image of `f` suffice to identify the radicals of the generated ideal and the extension of its contraction. The exponent may vary with the generator. Under the global power-image hypothesis, contraction is injective on radical ideals of `B`; the existing prime-spectrum injectivity criterion follows because prime ideals are radical.

- **Integrality reflects along nil kernels.** Let `K` be a commutative ring,
  let `A` and `B` be possibly noncommutative rings with their given `K`-algebra
  structures, and let `f : A →ₐ[K] B`. If every element killed by `f` is
  nilpotent, then integrality over `K` of `f a` implies integrality of `a`.
  The rings may lie in three independent universes; neither injectivity nor
  surjectivity of `f`, nor a uniform nilpotence exponent for its kernel,
  is required. The elementwise theorem
  `IsIntegral.of_isNilpotent_of_map_eq_zero` and its whole-algebra counterpart
  `Algebra.IsIntegral.of_isNilpotent_of_map_eq_zero` are in
  [`IntegralClosure.RingHom`](IntegralClosure/RingHom.lean). The latter reflects
  integrality of `B/K` to `A/K`; it does not require module finiteness.
- **Finiteness from powers of algebra generators.** Let `R` and `A` be
  commutative semirings with the given `R`-algebra structure. If a finite set
  generates `A` as an `R`-algebra and `C : Subalgebra R A` contains a positive
  power of each chosen generator, then the original `A` is finite as a module
  over `C` through the canonical inclusion action. Exponents may vary with the
  generator; no field, Noetherianity, finite type of `C/R`, or ring structure
  is assumed. The theorem
  [`Subalgebra.finite_of_adjoin_eq_top_of_forall_exists_pow_mem`](IntegralClosure/Subalgebra.lean)
  bounds powers in each singleton adjoin and multiplies the resulting
  `C`-submodule spans.
  Its finite-type, all-elements corollary is
  [`Subalgebra.finite_of_forall_exists_pow_mem`](IntegralClosure/Subalgebra.lean).
  The generator-only criterion applies to `ℕ[X²] ⊊ ℕ[X]`, with generator `X`
  and exponent `2`, where `1,X` span over `ℕ[X²]`. The all-elements condition
  fails in this example: the `X`-coefficient of `(1+X)^n` is `n` for every
  positive `n`. In general the bounded monomials span; they need not be a basis.
- **Prime-spectrum embeddings from powers in the image.** For commutative
  semirings `A` and `B` in independent universes and a homomorphism `f : A →+* B`,
  if every `b : B` has a positive natural power in `Set.range f`, then
  `PrimeSpectrum.comap f` is a topological embedding. The exponent may depend on
  `b`; neither injectivity nor surjectivity of `f` is assumed. The theorem
  [`PrimeSpectrum.isEmbedding_comap_of_forall_pow_mem_range`](IntegralClosure/Spectrum/Topology.lean)
  combines the inducing criterion
  `PrimeSpectrum.comap_isInducing_of_forall_pow_mem_range` with the existing
  [`PrimeSpectrum.comap_injective_of_forall_pow_mem_range`](IntegralClosure/Spectrum.lean).
  Mathlib's basic-open basis and power identities give the induced topology.
  This separates and generalizes the ring-free embedding component of
  `PrimeSpectrum.isHomeomorph_comap`, formalized in Mathlib by Christian Merten
  and Junyan Xu following the [Stacks Project, Tag 0BR8](https://stacks.math.columbia.edu/tag/0BR8).
  Mathlib's stronger homeomorphism theorem additionally assumes commutative rings
  and a kernel consisting of nilpotents. The surjective embedding criterion is
  recovered with exponent one, but not every localization embedding satisfies the
  premise. Over arbitrary commutative semirings this asserts no spectral
  surjectivity, homeomorphism, universal injectivity or closed range.
- **Integral closedness descends along a linear retraction.** For commutative
  rings `A` and `B`, an injective algebra map `A → B` into an integrally closed
  domain, together with an `A`-linear left inverse `B →ₗ[A] A`, gives integral
  closedness of `A`. The theorem
  [`IsIntegrallyClosed.of_linearRetract`](IntegralClosure/LinearRetract.lean#L43)
  derives the domain structure on `A` inside its proof. The retraction need not
  preserve multiplication, and the algebra map need not be integral.
- **Normal-domain descent from any field scalar extension.** For any field
  extension `l/k` and commutative `k`-algebra `A`, if `A ⊗[k] l` is a domain,
  then so is `A`; if the tensor product is also integrally closed, then so is
  `A`. The separate theorems
  [`isDomain_left`](IntegralClosure/TensorProduct.lean#L61) and
  [`isIntegrallyClosed_left`](IntegralClosure/TensorProduct.lean#L71) in
  `Algebra.TensorProduct` require no finite-dimensionality, algebraicity or
  separability assumption on the field extension.
- **Tensor-factor evaluation gives linear retractions.** For the same fields
  and algebra, any `k`-linear functional `f : l →ₗ[k] k` defines an `A`-linear
  [`rightLinearMap`](IntegralClosure/TensorProduct.lean#L45) from `A ⊗[k] l`
  to `A`, taking `a ⊗ₜ[k] b` to `a * algebraMap k A (f b)`. When `f 1 = 1`,
  [`rightLinearMap_includeLeft`](IntegralClosure/TensorProduct.lean#L54)
  proves it is a left inverse to `includeLeft`. Normalization is needed for
  this retraction equation, not for constructing the evaluation map; the
  functional and evaluation map need not be multiplicative.
- **Monic relations at inverses of units.** For a division semiring `R`, a
  semiring `S`, an arbitrary unital homomorphism `f : R →+* S` and a unit
  `a : Sˣ`, any nonzero polynomial relation over `R` at `a` yields a monic
  polynomial relation at `a⁻¹`. The results in
  [`IntegralClosure.Polynomial`](IntegralClosure/Polynomial.lean) require no
  coefficient centrality or commutativity of `S`. The more general semiring-source
  theorem assumes that the reversed polynomial's leading coefficient is a unit
  in `R`, without requiring the original polynomial to be nonzero.
- **A unit-constant criterion for two monic relations.** For arbitrary semirings
  `R` and `S`, a unital homomorphism `f : R →+* S` and `a : Sˣ`, monic
  polynomial relations at both `a` and `a⁻¹` exist exactly when a monic relation
  at `a` has constant coefficient a unit in `R`. When both relations exist,
  that constant coefficient can be chosen to be `1`. These results in
  [`IntegralClosure.Polynomial`](IntegralClosure/Polynomial.lean) use left
  coefficients and require no coefficient centrality. The unit condition is
  in the source semiring, not merely after applying `f`.
- **Units descend from a monic inverse relation.** For arbitrary semirings `R`
  and `S`, an injective homomorphism `f : R →+* S`, `r : R` and a unit
  `a : Sˣ` with `↑a = f r`, a monic polynomial relation over `R` at `a⁻¹`
  implies `IsUnit r`. The theorem
  `RingHom.isUnit_of_monic_eval₂_units_inv_eq_zero` in
  [`IntegralClosure.RingHom`](IntegralClosure/RingHom.lean) needs neither
  commutativity nor a second relation at `a`. Although stated with semiring
  instances, its hypotheses force both semirings to admit ring structures.

The five descent and tensor-evaluation declarations build on mathlib's
integral-closure, fraction-ring, tensor-product and projective-module duality
infrastructure. They establish
descent, not ascent, a converse or normalization. The descent theorems return
typeclass proofs for local use rather than installing global instances; the
tensor evaluation construction is noncomputable.

The reciprocal-evaluation lemmas generalize mathlib's commutative-target
identities using its polynomial-reversal and finite-sum APIs. Unit descent
refines its `RingHom.IsIntegral.isLocalHom` argument
and uses [Group Theory](https://github.com/FormalFrontier/group-theory)'s
zero-sum unit-transfer API. Subalgebra finiteness uses mathlib's adjoin-span
and adjoin-union formulas and finite generation of submodule products.

Import [`IntegralClosure`](IntegralClosure.lean) for all these families; the two
descent leaves are `IntegralClosure.LinearRetract` and
`IntegralClosure.TensorProduct`. The [API and examples below](#public-api-and-examples)
give the complete descent signatures, usage and proof explanations; the
[manual guide](docs/README.md) also covers power criteria and unit relations.

### Relative integrality and positive-power criteria

Let `R` be a commutative ring, `S` a possibly noncommutative ring, and
`f : R →+* S` a ring homomorphism; the rings may lie in independent universes.
An element `x : S` is integral relative to `f` (`f.IsIntegralElem x`) if some
monic polynomial `p : R[X]` satisfies `p.eval₂ f x = 0`.

- **Integrality is unchanged by positive powers.**
  [`RingHom.IsIntegralElem.pow`](IntegralClosure/RingHom.lean) shows that
  every natural power of an integral element is integral, including exponent
  zero. Conversely,
  [`of_pow`](IntegralClosure/RingHom.lean) and the simp lemma
  [`pow_iff`](IntegralClosure/RingHom.lean) require `0 < n`: integrality of
  `x ^ n` then implies, and is equivalent to, integrality of `x`.
- **Positive powers in the range imply an integral homomorphism.**
  [`RingHom.isIntegral_of_forall_pow_mem_range`](IntegralClosure/RingHom.lean)
  proves `f.IsIntegral` if each `x : S` has some positive power in `Set.range f`.
  Each element may have its own exponent; neither a uniform exponent nor
  surjectivity is required.

These criteria require no `Algebra` structure, centrality of coefficient images,
domain, nontriviality or finiteness hypothesis. Import `IntegralClosure.RingHom`
or the root `IntegralClosure`; the
[manual reference](docs/README.md#relative-integrality-and-power-criteria)
explains the arguments and the supporting polynomial evaluation lemmas.

### Jacobson radicals under integral homomorphisms

For arbitrary commutative rings `R` and `S` in independent universes and an
integral ring homomorphism `f : R →+* S`,
[`IntegralClosure.Jacobson`](IntegralClosure/Jacobson.lean) provides:

- `Ideal.comap_jacobson_of_isIntegral`: for every target ideal `J : Ideal S`,
  `J.jacobson.comap f = (J.comap f).jacobson`.
- `Ideal.map_jacobson_le_of_isIntegral`: for every source ideal `I : Ideal R`,
  `I.jacobson.map f ≤ (I.map f).jacobson`.
- `Ideal.map_le_jacobson_bot_of_isIntegral`: for every source ideal `I`,
  `I ≤ (⊥ : Ideal R).jacobson` implies
  `I.map f ≤ (⊥ : Ideal S).jacobson`.

No injectivity, surjectivity or nontriviality assumption is required.
Mathlib's surjective Jacobson formula also applies to possibly noncommutative
rings; the integral formula here assumes commutativity.

## Public API and examples

The [generated descent API snapshot](docs/API.md) retains the five descent and
evaluation declarations, their native display signatures and module documentation.
Its [generation manifest](docs/api-manifest.json) records the historical analysis,
not the current full API or these edited guides. The
[documentation guide](docs/README.md) gives current manual entry points for
relative integrality, power-containing subalgebras and unit-polynomial relations,
links the Jacobson module, and separates these from the historical reproduction
recipe.

### Linear-retraction and scalar-extension descent

Import `IntegralClosure.LinearRetract` for
`IsIntegrallyClosed.of_linearRetract`. For commutative rings `A` and `B` in
independent universes, with an `A`-algebra structure on `B`, the theorem takes
`[IsDomain B]`, `[IsIntegrallyClosed B]`, injectivity of `algebraMap A B`, and
an `A`-linear `r : B →ₗ[A] A` satisfying `r (algebraMap A B a) = a` for all `a`.
It produces `IsIntegrallyClosed A`, deriving a domain structure on `A` inside
the proof. Neither multiplicativity of `r` nor integrality of the algebra map
is required.

```lean
/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

import IntegralClosure.LinearRetract

/-! # README example: descent along a linear retraction -/

set_option warningAsError true
set_option linter.privateModule false

noncomputable section

universe u v

private theorem readme_linearRetract
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain B] [IsIntegrallyClosed B]
    (hinj : Function.Injective (algebraMap A B))
    (retract : B →ₗ[A] A) (hret : ∀ a, retract (algebraMap A B a) = a) :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_linearRetract hinj retract hret
```

Import `IntegralClosure.TensorProduct` for the four names in
`Algebra.TensorProduct` below, or `IntegralClosure` for all five descent and
evaluation names.
For fields `k`, `l`, a field extension `Algebra k l` and a commutative `k`-algebra
`A` (with three independent universes):

| Name | Use |
| --- | --- |
| `rightLinearMap k l A f` | For **any** `k`-linear `f : l →ₗ[k] k`, constructs an `A`-linear map `A ⊗[k] l →ₗ[A] A` evaluating `a ⊗ₜ[k] b` as `a * algebraMap k A (f b)`. It need not be multiplicative. |
| `rightLinearMap_includeLeft k l A f hf a` | If `hf : f 1 = 1`, evaluation after `includeLeft` returns `a`; this condition is only needed for retraction, not for constructing `rightLinearMap`. |
| `isDomain_left k l A` | Given `[IsDomain (A ⊗[k] l)]`, yields `IsDomain A` by injectivity of `includeLeft`. |
| `isIntegrallyClosed_left k l A` | Given `[IsDomain (A ⊗[k] l)]` and `[IsIntegrallyClosed (A ⊗[k] l)]`, yields `IsIntegrallyClosed A` using a functional with `f 1 = 1` and the generic retraction theorem. |

```lean
/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

import IntegralClosure

/-! # README examples: arbitrary field scalar extension -/

set_option warningAsError true
set_option linter.privateModule false

noncomputable section

open scoped TensorProduct

universe u v w

variable (k : Type u) (l : Type v) (A : Type w)
  [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]

private theorem readme_pureTensor (f : l →ₗ[k] k) (a : A) (b : l) :
    Algebra.TensorProduct.rightLinearMap k l A f (a ⊗ₜ[k] b) =
      a * algebraMap k A (f b) := by
  simp [Algebra.TensorProduct.rightLinearMap]

private theorem readme_retraction (f : l →ₗ[k] k) (hf : f 1 = 1) (a : A) :
    Algebra.TensorProduct.rightLinearMap k l A f
      (Algebra.TensorProduct.includeLeft (R := k) (S := A) (A := A) (B := l) a) = a :=
  Algebra.TensorProduct.rightLinearMap_includeLeft k l A f hf a

private theorem readme_domain [IsDomain (A ⊗[k] l)] : IsDomain A :=
  Algebra.TensorProduct.isDomain_left k l A

private theorem readme_normal [IsDomain (A ⊗[k] l)] [IsIntegrallyClosed (A ⊗[k] l)] :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have domain : IsDomain A := Algebra.TensorProduct.isDomain_left k l A
  exact ⟨domain, Algebra.TensorProduct.isIntegrallyClosed_left k l A⟩
```

The two descent conclusions are theorem-produced typeclass proofs: bind a result
locally with `have` (as above), or supply it where an instance is needed. These
examples impose no finite-dimensionality, algebraicity or separability hypothesis. The
`noncomputable section` permits the underlying choice of a normalized linear
functional; it is not an effective construction or a guarantee of definitional
equality beyond the displayed proved equations.

The generic proof embeds `FractionRing A` into `FractionRing B`. Integral
closedness in `B` supplies a representative `b` for an integral fraction; writing
the original fraction `a/s` and clearing the nonzero denominator gives
`algebraMap A B s * b = algebraMap A B a`. Applying the **A-linearity** of the
retraction yields `s * r b = a`, so `r b` represents the original fraction.
For a field extension, projective-module duality supplies a `k`-linear
functional taking `1` to `1`, even when the extension is infinite-dimensional.
Domain descent separately uses injectivity of `includeLeft`. These results
assert descent only; they do not provide ascent, a converse, or normalization.

`IntegralClosureTest.LeafClient` imports the direct leaves, and
`IntegralClosureTest.RootClient` imports only the root. Both hold named, private
client declarations for ordinary-import API checks; they add no public API.
The two complete Lean blocks above are stored verbatim in
[`ReadmeLinearRetract.lean`](IntegralClosureTest/ReadmeLinearRetract.lean) and
[`ReadmeTensorProduct.lean`](IntegralClosureTest/ReadmeTensorProduct.lean).
Their named private declarations are built by the default test target and are
included in the compiled-artifact proof audit; no anonymous proof example is
discarded after elaboration.

The descent results are independent of the organization of any motivating source.
Their mathematical motivation includes Ravi Vakil, *The Rising Sea: Foundations
of Algebraic Geometry*, October 21, 2025 draft, Exercise 5.4.M (physical/PDF
page 169), which asks whether finiteness in a forward normal-domain implication
is needed. This project develops a proof for arbitrary field extensions; the
book is a mathematical citation, not a formalization contributor or a
project-licensed asset.

## Build and test

Fetch the pinned mathlib cache before every build in a fresh checkout:

```sh
lake exe cache get
lake build
lake build IntegralClosureTest
```

The default `lake build` builds both the production library and the rootless
test library. To build individual production modules, run
`lake build IntegralClosure.LinearRetract IntegralClosure.TensorProduct IntegralClosure`.
Warnings are fatal in the mathematical leaves and test clients. The latter
exercise the public surface through ordinary imports rather than privileged
same-file access.

The project uses Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`.

