/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

import IntegralClosure

/-!
# Public-root clients

These stored private clients import only `IntegralClosure` and use its re-exported
mathematical interfaces. The field extension is arbitrary.
-/

set_option warningAsError true

noncomputable section

open scoped TensorProduct

universe u v w

private theorem root_linearRetract
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain B] [IsIntegrallyClosed B]
    (hinj : Function.Injective (algebraMap A B))
    (retract : B →ₗ[A] A) (hret : ∀ a, retract (algebraMap A B a) = a) :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_linearRetract hinj retract hret

private theorem root_tensor_retract (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    (f : l →ₗ[k] k) (hf : f 1 = 1) (a : A) :
    Algebra.TensorProduct.rightLinearMap k l A f
      (Algebra.TensorProduct.includeLeft (R := k) (S := A) (A := A) (B := l) a) = a :=
  Algebra.TensorProduct.rightLinearMap_includeLeft k l A f hf a

private theorem root_tensor_integrallyClosed (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    [IsDomain (A ⊗[k] l)] [IsIntegrallyClosed (A ⊗[k] l)] :
    IsIntegrallyClosed A :=
  Algebra.TensorProduct.isIntegrallyClosed_left k l A

private theorem root_tensor_domain (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    [IsDomain (A ⊗[k] l)] : IsDomain A :=
  Algebra.TensorProduct.isDomain_left k l A

private theorem root_tensor_pure (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    (f : l →ₗ[k] k) (a : A) (b : l) :
    Algebra.TensorProduct.rightLinearMap k l A f (a ⊗ₜ[k] b) =
      a * algebraMap k A (f b) := by
  simp [Algebra.TensorProduct.rightLinearMap]
