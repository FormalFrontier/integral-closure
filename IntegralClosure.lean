/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import IntegralClosure.ValuationRing
public import IntegralClosure.LinearRetract
public import IntegralClosure.TensorProduct
public import IntegralClosure.Jacobson

public import IntegralClosure.RingHom
public import IntegralClosure.Subalgebra
public import IntegralClosure.Spectrum
public import IntegralClosure.Spectrum.Topology

/-!
# Integral closure and field scalar extension

This root re-exports both independent-universe linear-retraction descent and
arbitrary-field-extension descent. Import either public leaf directly when only
one construction is needed. `IsIntegrallyClosed.of_linearRetract` takes an
injective algebra map and an A-linear left inverse; the tensor-product leaf
supplies `rightLinearMap`, its `includeLeft` retraction equation, and separate
domain and integral-closure descent theorems. The theorems do not install global
instances; their resulting typeclass proofs can be used locally. The root also
re-exports power criteria for integrality, finiteness and prime-spectrum embeddings,
and the valuation-domain criterion for local normal integral targets of arbitrary
integral homomorphisms from valuation domains.
-/

set_option warningAsError true
