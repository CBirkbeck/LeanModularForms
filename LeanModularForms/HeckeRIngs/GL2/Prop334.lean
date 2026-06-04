/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke

/-!
# Prop 3.34 — Gamma0MapUnits preservation under conjugation

For `g ∈ Δ₀(N)` and `h ∈ Γ₀(N)` whose rational conjugate `g⁻¹ · h · g` again
lies in `Γ₀(N)` (lifted through `mapGL ℚ`), the nebentypus-character values agree:
`Gamma0MapUnits (g⁻¹ · h · g) = Gamma0MapUnits h`. The main theorem
`Gamma0MapUnits_preserved_of_detCoprime` proves this in the coprime-determinant
case `gcd(det g, N) = 1`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
-/

namespace HeckeRing.GL2.Prop334

open Matrix CongruenceSubgroup HeckeRing.GLn Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups

private lemma inv_mul_mul_entry_smul_det {K : Type*} [Field K]
    (g h : Matrix (Fin 2) (Fin 2) K) (hdet : g.det ≠ 0) (i j : Fin 2) :
    (g⁻¹ * h * g) i j * g.det = (Matrix.adjugate g * h * g) i j := by
  rw [show g⁻¹ = (g.det)⁻¹ • Matrix.adjugate g by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']]
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- For `g = !![a, b; N·c, d]` with `det g ≠ 0` and `h = !![α, β; N·γ, δ]`
(promoted to `M₂(ℚ)`), the (1,1) entry of the rational conjugate satisfies
`(g⁻¹ · h · g)₁₁ · det g = a·d·δ + N · (a·b·γ - b·c·α - c·d·β)` over `ℚ`. -/
lemma matrix_fin_two_conj_entry_11_mod_eq (N : ℤ) (a b c d α β γ δ : ℤ)
    (hdet : (!![(a : ℚ), b; N * c, d]).det ≠ 0) :
    ((!![(a : ℚ), b; N * c, d])⁻¹ *
        !![(α : ℚ), β; N * γ, δ] * !![(a : ℚ), b; N * c, d]) 1 1 *
      (!![(a : ℚ), b; N * c, d]).det =
      (a : ℚ) * d * δ + N * (a * b * γ - b * c * α - c * d * β) := by
  rw [inv_mul_mul_entry_smul_det _ _ hdet]
  simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

private lemma isUnit_ad_of_det_coprime {N : ℕ} (a b c d : ℤ)
    (hdet : Int.gcd (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det N = 1) :
    IsUnit ((a * d : ℤ) : ZMod N) := by
  have hdetval : (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det = a * d - b * ((N : ℤ) * c) := by
    rw [Matrix.det_fin_two]; simp
  have heq : ((a * d : ℤ) : ZMod N) =
      (((!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det : ℤ) : ZMod N) := by
    rw [hdetval]; push_cast
    rw [show ((N : ZMod N)) = 0 from ZMod.natCast_self N]; ring
  rw [heq, ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  exact_mod_cast hdet

private lemma entry_11_mul_det_congr_mod
    (N : ℕ) (a b c d α β γ δ : ℤ) (h'₁₁ : ℤ)
    (hdet : (!![(a : ℚ), b; (N : ℚ) * c, d]).det ≠ 0)
    (h_conj_11 :
      ((!![(a : ℚ), b; (N : ℚ) * c, d])⁻¹ *
          !![(α : ℚ), β; (N : ℚ) * γ, δ] * !![(a : ℚ), b; (N : ℚ) * c, d]) 1 1 =
        (h'₁₁ : ℚ)) :
    ((h'₁₁ * (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det : ℤ) : ZMod N) =
      ((a * d * δ : ℤ) : ZMod N) := by
  have hdet_int : (!![(a : ℚ), b; ((N : ℤ) : ℚ) * c, d]).det ≠ 0 := mod_cast hdet
  have hQ := matrix_fin_two_conj_entry_11_mod_eq (N : ℤ) a b c d α β γ δ hdet_int
  have hcastN : ((N : ℤ) : ℚ) = (N : ℚ) := by push_cast; rfl
  have hdet_eq : (!![(a : ℚ), b; (N : ℚ) * c, d]).det =
      ((!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det : ℚ) := by
    simp only [Matrix.det_fin_two_of]; push_cast; ring
  rw [hcastN, h_conj_11, hdet_eq] at hQ
  have hZ : h'₁₁ * (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det =
      a * d * δ + (N : ℤ) * (a * b * γ - b * c * α - c * d * β) := mod_cast hQ
  rw [hZ]; push_cast; ring_nf; simp

end HeckeRing.GL2.Prop334
