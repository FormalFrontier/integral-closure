/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

import IntegralClosure.LinearRetract
import IntegralClosure.TensorProduct

/-!
# Direct-leaf clients

Stored private clients test both public leaves without importing the aggregate
root. Their separate universe parameters and arbitrary field extension deliberately
avoid dimension, algebraicity, separability and multiplicativity assumptions.
-/

set_option warningAsError true

noncomputable section

open scoped TensorProduct

universe u v w

private theorem linearRetract_descent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain B] [IsIntegrallyClosed B]
    (hinj : Function.Injective (algebraMap A B))
    (retract : B →ₗ[A] A) (hret : ∀ a, retract (algebraMap A B a) = a) :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_linearRetract hinj retract hret

private theorem tensor_retract
    (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    (f : l →ₗ[k] k) (hf : f 1 = 1) (a : A) :
    Algebra.TensorProduct.rightLinearMap k l A f
      (Algebra.TensorProduct.includeLeft (R := k) (S := A) (A := A) (B := l) a) = a :=
  Algebra.TensorProduct.rightLinearMap_includeLeft k l A f hf a

private theorem tensor_domain
    (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    [IsDomain (A ⊗[k] l)] : IsDomain A :=
  Algebra.TensorProduct.isDomain_left k l A

private theorem tensor_integrallyClosed
    (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    [IsDomain (A ⊗[k] l)] [IsIntegrallyClosed (A ⊗[k] l)] :
    IsIntegrallyClosed A :=
  Algebra.TensorProduct.isIntegrallyClosed_left k l A

private theorem identity_linearRetract (k : Type u) [Field k] : IsIntegrallyClosed k :=
  IsIntegrallyClosed.of_linearRetract (A := k) (B := k)
    (by simpa using (Function.injective_id : Function.Injective (id : k → k)))
    (LinearMap.id : k →ₗ[k] k) (by intro a; simp)

private theorem tensor_pure (k : Type u) (l : Type v) (A : Type w)
    [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]
    (f : l →ₗ[k] k) (a : A) (b : l) :
    Algebra.TensorProduct.rightLinearMap k l A f (a ⊗ₜ[k] b) =
      a * algebraMap k A (f b) := by
  simp [Algebra.TensorProduct.rightLinearMap]
