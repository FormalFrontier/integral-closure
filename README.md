# integral-closure

Licensed under the Apache License, Version 2.0 (see [LICENSE](LICENSE)).
**Authors: Formal Frontier Agents.** The original production proofs and
declarations were contributed by Atlas. Other Formal Frontier contributors
assembled the ordinary module interfaces and stored downstream clients; Folio
contributed the headline summaries. Formal Frontier agents, including AI agents,
wrote and checked the project-specific code and documentation. The collective
author credit does not assert copyright ownership.

Reusable Lean theory of integral closure and normal-domain descent.

## Headline results

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

These five public declarations build on mathlib's integral-closure, fraction-ring,
tensor-product and projective-module duality infrastructure. They establish
descent, not ascent, a converse or normalization. The descent theorems return
typeclass proofs for local use rather than installing global instances; the
tensor evaluation construction is noncomputable.

Import [`IntegralClosure`](IntegralClosure.lean) for both criteria, or import
`IntegralClosure.LinearRetract` and `IntegralClosure.TensorProduct` directly.
The [API and examples below](#public-api-and-examples) give the complete
signatures, usage and proof explanations.

## Public API and examples

The [generated API reference](docs/API.md) includes all five public declarations,
their complete native display signatures and module documentation. Its
[generation manifest](docs/api-manifest.json) binds the analyzed source and pins;
[reproduction instructions](docs/README.md) describe the separate pinned tool.

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
`Algebra.TensorProduct` below, or `IntegralClosure` for all five public names.
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

These results are independent of the organization of any motivating source.
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
`e37d88a26f3791ed5a93daa1f949af1021b8d103`.

### Initial build baseline

In a Linux Hive container with a 23 GiB memory limit and two Lean threads,
the seven sequential clean library/example module builds took 35.3 seconds in
total after fetching the matching mathlib cache. The largest recorded child
maximum resident set among cache/build/fresh-source commands was approximately
1.37 GiB. These are observed command measurements, not total container peaks or
portable requirements. They exclude documentation-tool compilation and separate
proof rechecking. Unchanged dependencies used the pinned precompiled cache;
the library's own sources were compiled from absent local outputs. Different
hardware, cache/network state and tool workloads will change these costs.

Release candidates require applicable independent review, complete verification
and redistribution assessment. Existing build and standard-axiom evidence can be
reused when its checked inputs and coverage match; documentation-only changes
receive lightweight documentation and metadata checks. Schema validity alone
does not establish release acceptance.
