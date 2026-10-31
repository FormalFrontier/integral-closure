/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import IntegralClosure.RingHom

/-! The algebra form is recovered by choosing the algebra map. -/

universe u v

example {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
    {x : S} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R (x ^ n)) : IsIntegral R x := by
  exact RingHom.IsIntegralElem.of_pow (f := algebraMap R S) hn hx
