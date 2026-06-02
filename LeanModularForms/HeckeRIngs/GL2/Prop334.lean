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

/-- For `g = !![a, b; N·c, d]` and `h = !![α, β; N·γ, δ]` in `M₂(ℤ)`,
the (1,1) entry of `adj(g) · h · g` equals
`a·d·δ + N · (a·b·γ - b·c·α - c·d·β)`. -/
lemma adj_mul_mul_entry_11_eq (N : ℤ) (a b c d α β γ δ : ℤ) :
    ((Matrix.adjugate !![a, b; N * c, d] *
        !![α, β; N * γ, δ]) * !![a, b; N * c, d]) 1 1 =
      a * d * δ + N * (a * b * γ - b * c * α - c * d * β) := by
  simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- For `g = !![a, b; N·c, d]` and `h = !![α, β; N·γ, δ]` in `M₂(ℤ)`,
the (0,0) entry of `adj(g) · h · g` equals
`a·d·α + N · (-a·b·γ + c·d·β - b·c·δ)`. -/
lemma adj_mul_mul_entry_00_eq (N : ℤ) (a b c d α β γ δ : ℤ) :
    ((Matrix.adjugate !![a, b; N * c, d] *
        !![α, β; N * γ, δ]) * !![a, b; N * c, d]) 0 0 =
      a * d * α + N * (-(a * b * γ) + c * d * β - b * c * δ) := by
  simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

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

/-- For `g = !![a, b; N·c, d]` with `det g ≠ 0` and `h = !![α, β; N·γ, δ]`
(promoted to `M₂(ℚ)`), the (0,0) entry of the rational conjugate satisfies
`(g⁻¹ · h · g)₀₀ · det g = a·d·α + N · (-a·b·γ + c·d·β - b·c·δ)` over `ℚ`. -/
lemma matrix_fin_two_conj_entry_00_mod_eq (N : ℤ) (a b c d α β γ δ : ℤ)
    (hdet : (!![(a : ℚ), b; N * c, d]).det ≠ 0) :
    ((!![(a : ℚ), b; N * c, d])⁻¹ *
        !![(α : ℚ), β; N * γ, δ] * !![(a : ℚ), b; N * c, d]) 0 0 *
      (!![(a : ℚ), b; N * c, d]).det =
      (a : ℚ) * d * α + N * (-(a * b * γ) + c * d * β - b * c * δ) := by
  rw [inv_mul_mul_entry_smul_det _ _ hdet]
  simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Divisibility corollary of `adj_mul_mul_entry_11_eq`: the difference between
the (1,1) entry of `adj g * h * g` and `a·d·δ` is an `N`-multiple. -/
lemma N_dvd_adj_mul_mul_entry_11_sub (N : ℤ) (a b c d α β γ δ : ℤ) :
    N ∣ ((Matrix.adjugate !![a, b; N * c, d] *
        !![α, β; N * γ, δ]) * !![a, b; N * c, d]) 1 1 - a * d * δ := by
  rw [adj_mul_mul_entry_11_eq]
  exact ⟨a * b * γ - b * c * α - c * d * β, by ring⟩

/-- Divisibility corollary of `adj_mul_mul_entry_00_eq`: the difference between
the (0,0) entry of `adj g * h * g` and `a·d·α` is an `N`-multiple. -/
lemma N_dvd_adj_mul_mul_entry_00_sub (N : ℤ) (a b c d α β γ δ : ℤ) :
    N ∣ ((Matrix.adjugate !![a, b; N * c, d] *
        !![α, β; N * γ, δ]) * !![a, b; N * c, d]) 0 0 - a * d * α := by
  rw [adj_mul_mul_entry_00_eq]
  exact ⟨-(a * b * γ) + c * d * β - b * c * δ, by ring⟩

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

private lemma conj_matrix_entry_11_eq_intCast
    (gG : GL (Fin 2) ℚ) (hS h'S : SL(2, ℤ))
    (a b c d α β γ δ N : ℚ)
    (hA_rat : (↑gG : Matrix (Fin 2) (Fin 2) ℚ) = !![a, b; N * c, d])
    (hAh_rat : ((mapGL ℚ hS) : Matrix (Fin 2) (Fin 2) ℚ) = !![α, β; N * γ, δ])
    (h'_conj : (mapGL ℚ h'S : GL (Fin 2) ℚ) = gG⁻¹ * mapGL ℚ hS * gG) :
    ((!![a, b; N * c, d])⁻¹ * !![α, β; N * γ, δ] * !![a, b; N * c, d]) 1 1 =
      ((h'S).val 1 1 : ℚ) := by
  have h_mat_eq : ((mapGL ℚ h'S) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((gG⁻¹ : Matrix _ _ ℚ) *
        (mapGL ℚ hS : Matrix _ _ ℚ) * (gG : Matrix _ _ ℚ)) := by
    simpa [Matrix.GeneralLinearGroup.coe_mul] using
      congr_arg (fun X : GL (Fin 2) ℚ ↦ (X : Matrix (Fin 2) (Fin 2) ℚ)) h'_conj
  have h_entry := congr_fun (congr_fun h_mat_eq 1) 1
  rw [hA_rat, hAh_rat, mapGL_coe_matrix] at h_entry
  simpa using h_entry.symm

private lemma conj_entry_11_intCast_eq_mod {N : ℕ}
    (a b c d α β γ δ h'₁₁ : ℤ)
    (hdet_ne : (!![(a : ℚ), b; (N : ℚ) * c, d]).det ≠ 0)
    (hdet_cop : Int.gcd (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det N = 1)
    (h_conj_11 :
      ((!![(a : ℚ), b; (N : ℚ) * c, d])⁻¹ *
          !![(α : ℚ), β; (N : ℚ) * γ, δ] * !![(a : ℚ), b; (N : ℚ) * c, d]) 1 1 =
        (h'₁₁ : ℚ)) :
    (h'₁₁ : ZMod N) = (δ : ZMod N) := by
  set detA : ℤ := (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det with hdetA_def
  have h_mod : ((h'₁₁ * detA : ℤ) : ZMod N) = ((a * d * δ : ℤ) : ZMod N) :=
    entry_11_mul_det_congr_mod N a b c d α β γ δ h'₁₁ hdet_ne h_conj_11
  have had_unit : IsUnit ((a * d : ℤ) : ZMod N) :=
    isUnit_ad_of_det_coprime a b c d hdet_cop
  have hdetA_mod : ((detA : ℤ) : ZMod N) = ((a * d : ℤ) : ZMod N) := by
    rw [hdetA_def]
    simp only [Matrix.det_fin_two_of]; push_cast
    rw [show ((N : ZMod N)) = 0 from ZMod.natCast_self N]; ring
  have h_mod' : (h'₁₁ : ZMod N) * ((a * d : ℤ) : ZMod N) =
      ((a * d : ℤ) : ZMod N) * (δ : ZMod N) := by
    calc (h'₁₁ : ZMod N) * ((a * d : ℤ) : ZMod N)
        = (h'₁₁ : ZMod N) * ((detA : ℤ) : ZMod N) := by rw [hdetA_mod]
      _ = ((h'₁₁ * detA : ℤ) : ZMod N) := by push_cast; ring
      _ = ((a * d * δ : ℤ) : ZMod N) := h_mod
      _ = ((a * d : ℤ) : ZMod N) * (δ : ZMod N) := by push_cast; ring
  rw [mul_comm _ ((a * d : ℤ) : ZMod N)] at h_mod'
  exact had_unit.mul_left_cancel h_mod'

private lemma delta_elt_intCast_matrix_form {N : ℕ} [NeZero N]
    (g : (Gamma0_pair N).Δ) :
    ∃ a b c d : ℤ, (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(a : ℚ), (b : ℚ); (N : ℚ) * (c : ℚ), (d : ℚ)] := by
  obtain ⟨_, _, A, hA_eq, ⟨c, hc⟩, _⟩ := g.2
  refine ⟨A 0 0, A 0 1, c, A 1 1, ?_⟩
  have hA_reshape : A = !![A 0 0, A 0 1; (N : ℤ) * c, A 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hc]
  rw [hA_eq, hA_reshape]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma gamma0_elt_intCast_matrix_form {N : ℕ} (h : ↥(Gamma0 N)) :
    ∃ α β γ δ : ℤ, ((mapGL ℚ (h : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![(α : ℚ), (β : ℚ); (N : ℚ) * (γ : ℚ), (δ : ℚ)] ∧
      (δ : ZMod N) = ((h : SL(2, ℤ)).val 1 1 : ZMod N) := by
  set Ah : Matrix (Fin 2) (Fin 2) ℤ := (h : SL(2, ℤ)).val with hAh_def
  obtain ⟨γ, hγ⟩ : (N : ℤ) ∣ Ah 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h.property)
  refine ⟨Ah 0 0, Ah 0 1, γ, Ah 1 1, ?_, by rw [hAh_def]⟩
  rw [mapGL_coe_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, ← hAh_def, hγ]

/-- For `g ∈ Δ₀(N)` with `gcd(det g, N) = 1` and `h h' ∈ Γ₀(N)` related by
`mapGL ℚ h' = g⁻¹ · mapGL ℚ h · g` in `GL₂(ℚ)`, the nebentypus character values
agree: `Gamma0MapUnits h' = Gamma0MapUnits h`. This is the coprime-determinant
case of Shimura Proposition 3.34. -/
theorem Gamma0MapUnits_preserved_of_detCoprime {N : ℕ} [NeZero N]
    (g : (Gamma0_pair N).Δ)
    (h_det_coprime : ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        A.map (Int.cast : ℤ → ℚ) → Int.gcd A.det N = 1)
    (h h' : ↥(Gamma0 N))
    (h'_conj : (mapGL ℚ (h' : SL(2, ℤ)) : GL (Fin 2) ℚ) =
      (g : GL (Fin 2) ℚ)⁻¹ * mapGL ℚ (h : SL(2, ℤ)) * (g : GL (Fin 2) ℚ)) :
    Gamma0MapUnits h' = Gamma0MapUnits h := by
  obtain ⟨a, b, c, d, hA_rat⟩ := delta_elt_intCast_matrix_form g
  obtain ⟨α, β, γ, δ, hAh_rat, hδ_eq⟩ := gamma0_elt_intCast_matrix_form h
  set h'₁₁ : ℤ := (h' : SL(2, ℤ)).val 1 1
  have hdet_ne : (!![(a : ℚ), (b : ℚ); (N : ℚ) * (c : ℚ), (d : ℚ)]).det ≠ 0 :=
    hA_rat ▸ Matrix.GeneralLinearGroup.det_ne_zero g.val
  have hdet_cop : Int.gcd (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det N = 1 := by
    refine h_det_coprime _ ?_
    rw [hA_rat]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  have h_conj_11 := conj_matrix_entry_11_eq_intCast (g : GL (Fin 2) ℚ)
    (h : SL(2, ℤ)) (h' : SL(2, ℤ)) a b c d α β γ δ N hA_rat hAh_rat h'_conj
  have h'₁₁_eq_δ : (h'₁₁ : ZMod N) = (δ : ZMod N) :=
    conj_entry_11_intCast_eq_mod a b c d α β γ δ h'₁₁ hdet_ne hdet_cop h_conj_11
  have hGamma0Map : Gamma0Map N h' = Gamma0Map N h := by
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← hδ_eq]; exact h'₁₁_eq_δ
  ext
  rw [Gamma0MapUnits_val, Gamma0MapUnits_val, hGamma0Map]

end HeckeRing.GL2.Prop334
