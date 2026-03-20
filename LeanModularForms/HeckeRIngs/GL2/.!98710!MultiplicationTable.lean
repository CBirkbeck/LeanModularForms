/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GLn.Degree
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Shimura Theorem 3.24: Multiplication Table for GL₂ Hecke Algebra

The 7 multiplication identities for the n=2 Hecke algebra.

## Main results

* `thm324_2` — `T(1,pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2
* `thm324_3` — `T(m) · T(n) = Σ d · T(d,d) · T(mn/d²)`
* `thm324_4` — `T(pʳ) · T(pˢ) = Σ pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})` for r ≤ s
* `thm324_5` — `T(p) · T(1,pᵏ) = T(1,p^{k+1}) + m · T(p,pᵏ)` (key computation)
* `thm324_6` — `deg(T(pⁱ, p^{i+k})) = p^{k−1}(p+1)` (wrapping existing)
* `thm324_6_scalar` — `deg(T(c,c)) = 1` (wrapping existing)
* `thm324_7` — `deg(T(m)) = σ₁(m)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2
open scoped ArithmeticFunction.sigma

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

/-! ### Identity 1: T(m) = Σ T(a,d) — definitional

Shimura's T(m) is defined as `T_sum m`, which is exactly the sum
`Σ_{a ∣ m, a²∣m} T(a, m/a)`. This identity is the definition itself. -/

/-! ### Identity 2: Telescoping -/

section Telescoping

/-- `T_ad(p^i, p^d)` unfolds to `T_ad` when `i ≤ d`. -/
private lemma T_ad_ppow (i d : ℕ) (hid : i ≤ d) :
    T_ad (p ^ i) (p ^ d) =
    T_ad (p ^ i) (p ^ d)
      (Nat.pow_dvd_pow p hid) := by
  unfold T_ad
