/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import IntegralClosure.LinearRetract
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Normal-domain descent from a field scalar extension

For a field extension `l/k` and a commutative `k`-algebra `A`, this file proves
that the domain and integral-closedness properties of `A ⊗[k] l` descend to
`A`. No finite-dimensionality, algebraicity or separability hypothesis on
`l/k` is needed; k, l and A live in independent universes. The two descent
claims are separate theorems, not global instances.
-/

set_option warningAsError true

noncomputable section

public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable (k : Type u) (l : Type v) (A : Type w)
  [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]

/-- Applying any k-linear functional `f : l →ₗ[k] k` to the right factor gives an
A-linear map from `A ⊗[k] l` back to A. It evaluates `a ⊗ₜ[k] b` as
`a * algebraMap k A (f b)`; neither `f 1 = 1` nor multiplicativity is needed.
The definition is noncomputable and exposed for downstream simplification; the
pure-tensor calculation follows from its universal-property construction, not
from an advertised definitional equality. -/
@[expose]
def rightLinearMap (f : l →ₗ[k] k) : A ⊗[k] l →ₗ[A] A :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a ↦ a • ((Algebra.linearMap k A).comp f)
      map_add' := fun a b ↦ by simp [add_smul]
      map_smul' := fun a b ↦ by simp [mul_smul] }

/-- If the functional sends `1` to `1`, evaluating after `includeLeft` is the
identity on A. This supplies the A-linear left inverse used in descent; it does
not assert that `rightLinearMap` preserves multiplication. -/
theorem rightLinearMap_includeLeft (f : l →ₗ[k] k) (hf : f 1 = 1) (a : A) :
    rightLinearMap k l A f (includeLeft (R := k) (S := A) (A := A) (B := l) a) = a := by
  simp [rightLinearMap, includeLeft_apply, hf]

/-- If a scalar extension of a commutative algebra along a field extension is a
domain, then the original algebra is a domain, by injectivity of `includeLeft`.
This theorem returns a typeclass proof; it installs no global instance. -/
theorem isDomain_left [IsDomain (A ⊗[k] l)] : IsDomain A :=
  (includeLeft_injective (S := A) (algebraMap k l).injective).isDomain
    (includeLeft (R := k) (S := A) (A := A) (B := l)).toRingHom

/-- If a scalar extension of a commutative algebra along a field extension is
an integrally closed domain, then the original algebra is integrally closed.
Projective-module duality supplies a k-linear functional with `f 1 = 1` for any
field extension; `rightLinearMap_includeLeft` and the generic linear-retraction
theorem give descent. No finite-dimensionality or multiplicative retraction is
needed, and this theorem installs no global instance. -/
theorem isIntegrallyClosed_left
    [IsDomain (A ⊗[k] l)] [IsIntegrallyClosed (A ⊗[k] l)] :
    IsIntegrallyClosed A := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k (x := (1 : l)) one_ne_zero
  exact IsIntegrallyClosed.of_linearRetract
    (includeLeft_injective (S := A) (algebraMap k l).injective)
    (rightLinearMap k l A f) (rightLinearMap_includeLeft k l A f hf)

end Algebra.TensorProduct

end
