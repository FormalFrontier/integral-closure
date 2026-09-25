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
