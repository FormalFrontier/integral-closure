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
