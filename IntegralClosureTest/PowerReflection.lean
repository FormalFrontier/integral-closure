/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import IntegralClosure.RingHom

/-! The algebra form is recovered by choosing the algebra map. -/

universe u v

example {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
    {x : S} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R (x ^ n)) : IsIntegral R x := by
  exact RingHom.IsIntegralElem.of_pow (f := algebraMap R S) hn hx

-- Powers from the raw API can be combined by the stock algebraic API.
example {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} (hx : (algebraMap R S).IsIntegralElem x) :
    IsIntegral R (x ^ 2 + x ^ 3) := by
  have hx₂ : IsIntegral R (x ^ 2) := RingHom.IsIntegralElem.pow hx 2
  have hx₃ : IsIntegral R (x ^ 3) := RingHom.IsIntegralElem.pow hx 3
  exact hx₂.add hx₃
