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

end HeckeRing.GL2.Prop334
