/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import IntegralClosure.LinearRetract
public import IntegralClosure.TensorProduct

/-!
# Integral closure and field scalar extension

This root re-exports both independent-universe linear-retraction descent and
arbitrary-field-extension descent. Import either public leaf directly when only
one construction is needed. `IsIntegrallyClosed.of_linearRetract` takes an
injective algebra map and an A-linear left inverse; the tensor-product leaf
supplies `rightLinearMap`, its `includeLeft` retraction equation, and separate
domain and integral-closure descent theorems. The theorems do not install global
instances; their resulting typeclass proofs can be used locally.
-/

set_option warningAsError true
