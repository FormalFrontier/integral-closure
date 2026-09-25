# Generated API reference

Complete public API of integral-closure: five declarations in two mathematical leaves.
Import `IntegralClosure` for both leaves. Four test modules contain private checked
clients and README examples, not additional public API.

Signatures below are native doc-gen4 display signatures with all displayed implicit
arguments retained, not declarations with proof bodies. Short names use the source
namespace and imports; universe parameters are arbitrary. Module documentation
is extracted verbatim from the exact source. All source links are relative to this
checkout. See [generation and provenance](README.md), [exact input manifest](api-manifest.json)
and the [mathematical overview](../README.md).

## Module `IntegralClosure.LinearRetract`

> # Integral closure descends along linear retractions
>
> This file proves that an injective algebra map into an integrally closed domain
> descends integral closedness when it admits a linear retraction. The proof does
> not require the map to be integral or the retraction to preserve multiplication.
> Commutative rings A and B may inhabit independent universes. Domain and
> integral-closedness assumptions are on B; the domain structure on A is obtained
> from the injective algebra map inside the theorem.

[Module source](../IntegralClosure/LinearRetract.lean)

### IsIntegrallyClosed.of_linearRetract

```lean
theorem IsIntegrallyClosed.of_linearRetract {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsDomain B] [IsIntegrallyClosed B] (hinj : Function.Injective ⇑(algebraMap A B)) (r : B →ₗ[A] A) (hr : ∀ (a : A), r ((algebraMap A B) a) = a) : IsIntegrallyClosed A
```

An injective algebra map into an integrally closed domain descends integral
closedness when it has an A-linear left inverse `r`. Injectivity is an explicit
argument. No ring-homomorphism property of `r` or integrality of the map is
assumed.

The proof transfers an integral fraction into the fraction ring of B, where it
equals some `b : B`. After writing the original fraction as `a/s`, its equality
in the fraction ring clears to `algebraMap A B s * b = algebraMap A B a`.
A-linearity of `r` then gives `s * r b = a`, proving that `r b` represents the
fraction over A. Nonzero denominators and injectivity justify the cancellations;
`r` is never used as a multiplicative map.

[Source](../IntegralClosure/LinearRetract.lean#L32) (line 32).

## Module `IntegralClosure.TensorProduct`

> # Normal-domain descent from a field scalar extension
>
> For a field extension `l/k` and a commutative `k`-algebra `A`, this file proves
> that the domain and integral-closedness properties of `A ⊗[k] l` descend to
> `A`. No finite-dimensionality, algebraicity or separability hypothesis on
> `l/k` is needed; k, l and A live in independent universes. The two descent
> claims are separate theorems, not global instances.

[Module source](../IntegralClosure/TensorProduct.lean)

### Algebra.TensorProduct.rightLinearMap

```lean
def Algebra.TensorProduct.rightLinearMap (k : Type u) (l : Type v) (A : Type w) [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A] (f : l →ₗ[k] k) : TensorProduct k A l →ₗ[A] A
```

Applying any k-linear functional `f : l →ₗ[k] k` to the right factor gives an
A-linear map from `A ⊗[k] l` back to A. It evaluates `a ⊗ₜ[k] b` as
`a * algebraMap k A (f b)`; neither `f 1 = 1` nor multiplicativity is needed.
The definition is noncomputable and exposed for downstream simplification; the
pure-tensor calculation follows from its universal-property construction, not
from an advertised definitional equality.

[Source](../IntegralClosure/TensorProduct.lean#L38) (line 38).

### Algebra.TensorProduct.rightLinearMap_includeLeft

```lean
theorem Algebra.TensorProduct.rightLinearMap_includeLeft (k : Type u) (l : Type v) (A : Type w) [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A] (f : l →ₗ[k] k) (hf : f 1 = 1) (a : A) : (rightLinearMap k l A f) (includeLeft a) = a
```

If the functional sends `1` to `1`, evaluating after `includeLeft` is the
identity on A. This supplies the A-linear left inverse used in descent; it does
not assert that `rightLinearMap` preserves multiplication.

[Source](../IntegralClosure/TensorProduct.lean#L51) (line 51).

### Algebra.TensorProduct.isDomain_left

```lean
theorem Algebra.TensorProduct.isDomain_left (k : Type u) (l : Type v) (A : Type w) [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A] [IsDomain (TensorProduct k A l)] : IsDomain A
```

If a scalar extension of a commutative algebra along a field extension is a
domain, then the original algebra is a domain, by injectivity of `includeLeft`.
This theorem returns a typeclass proof; it installs no global instance.

[Source](../IntegralClosure/TensorProduct.lean#L58) (line 58).

### Algebra.TensorProduct.isIntegrallyClosed_left

```lean
theorem Algebra.TensorProduct.isIntegrallyClosed_left (k : Type u) (l : Type v) (A : Type w) [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A] [IsDomain (TensorProduct k A l)] [IsIntegrallyClosed (TensorProduct k A l)] : IsIntegrallyClosed A
```

If a scalar extension of a commutative algebra along a field extension is
an integrally closed domain, then the original algebra is integrally closed.
Projective-module duality supplies a k-linear functional with `f 1 = 1` for any
field extension; `rightLinearMap_includeLeft` and the generic linear-retraction
theorem give descent. No finite-dimensionality or multiplicative retraction is
needed, and this theorem installs no global instance.

[Source](../IntegralClosure/TensorProduct.lean#L65) (line 65).

## Module `IntegralClosure`

> # Integral closure and field scalar extension
>
> This root re-exports both independent-universe linear-retraction descent and
> arbitrary-field-extension descent. Import either public leaf directly when only
> one construction is needed. `IsIntegrallyClosed.of_linearRetract` takes an
> injective algebra map and an A-linear left inverse; the tensor-product leaf
> supplies `rightLinearMap`, its `includeLeft` retraction equation, and separate
> domain and integral-closure descent theorems. The theorems do not install global
> instances; their resulting typeclass proofs can be used locally.

[Module source](../IntegralClosure.lean)

## Module `IntegralClosureTest.LeafClient`

> # Direct-leaf clients
>
> Stored private clients test both public leaves without importing the aggregate
> root. Their separate universe parameters and arbitrary field extension deliberately
> avoid dimension, algebraicity, separability and multiplicativity assumptions.

[Module source](../IntegralClosureTest/LeafClient.lean)

## Module `IntegralClosureTest.RootClient`

> # Public-root clients
>
> These stored private clients import only `IntegralClosure` and use its re-exported
> mathematical interfaces. The field extension is arbitrary.

[Module source](../IntegralClosureTest/RootClient.lean)

## Module `IntegralClosureTest.ReadmeLinearRetract`

> # README example: descent along a linear retraction

[Module source](../IntegralClosureTest/ReadmeLinearRetract.lean)

## Module `IntegralClosureTest.ReadmeTensorProduct`

> # README examples: arbitrary field scalar extension

[Module source](../IntegralClosureTest/ReadmeTensorProduct.lean)
