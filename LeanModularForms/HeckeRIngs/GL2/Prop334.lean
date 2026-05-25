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

This file carries out the matrix-algebraic heart of Shimura Proposition 3.34
(Tickets `P334-A` and `P334-B`).

## Goal of Prop 3.34

For `g ∈ Δ₀(N)` and `h ∈ Γ₀(N)` such that the rational conjugate
`g⁻¹ · h · g ∈ Γ₀(N)` (lifted through `mapGL ℚ`), the nebentypus-character
values agree:
```
Gamma0MapUnits (g⁻¹ · h · g) = Gamma0MapUnits h.
```
The upshot for Hecke theory is that `heckeSlash_gen D` preserves the
character eigenspace `modFormCharSpace k χ` for arbitrary Dirichlet
characters `χ`.

## Main lemmas (P334-A)

* `adj_mul_mul_entry_11_eq` — the integer identity
  `(adj g * h * g)₁₁ = a·d·δ + N·(a·b·γ - b·c·α - c·d·β)` for
  `g = !![a, b; N·c, d]` and `h = !![α, β; N·γ, δ]`.
* `adj_mul_mul_entry_00_eq` — the analogous integer identity
  `(adj g * h * g)₀₀ = a·d·α + N·(-a·b·γ + c·d·β - b·c·δ)`.
* `matrix_fin_two_conj_entry_11_mod_eq` — the ℚ-valued consequence
  `(g⁻¹ · h · g)₁₁ · det g = a·d·δ + N·stuff` (hence `≡ a·d·δ (mod N)`
  after integrality of the conjugate).
* `matrix_fin_two_conj_entry_00_mod_eq` — analogous for the (0,0) entry.

## Main theorem (P334-B)

* `Gamma0MapUnits_preserved_of_detCoprime` — for `g ∈ Δ₀(N)` with
  `gcd(det g, N) = 1`, conjugation by `g` preserves `Gamma0MapUnits`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
-/

namespace HeckeRing.GL2.Prop334

open Matrix CongruenceSubgroup HeckeRing.GLn Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups

/-! ### Integer-level identities for `adj g * h * g` entries

Working purely over ℤ with `g = !![a, b; N·c, d]` and `h = !![α, β; N·γ, δ]`,
we expand the products `adj g * h * g` and read off the (0,0) and (1,1)
entries. These expansions are the algebraic heart of Prop 3.34: the
`N`-multiple portion vanishes mod `N`, leaving the "diagonal part"
`a·d·α` resp. `a·d·δ`. -/

/-- Core matrix-entry identity for Shimura Prop 3.34 — integer form.

For `g = !![a, b; N·c, d]` and `h = !![α, β; N·γ, δ]` in `M₂(ℤ)`,
the (1,1) entry of `adj(g) · h · g` equals
`a·d·δ + N · (a·b·γ - b·c·α - c·d·β)`.

This is an unconditional polynomial identity (no `det g ≠ 0` hypothesis),
obtained by expanding the 2×2 matrix product. It is the source of the
mod-`N` congruence driving Prop 3.34. -/
lemma adj_mul_mul_entry_11_eq (N : ℤ) (a b c d α β γ δ : ℤ) :
    ((Matrix.adjugate !![a, b; N * c, d] *
        !![α, β; N * γ, δ]) * !![a, b; N * c, d]) 1 1 =
      a * d * δ + N * (a * b * γ - b * c * α - c * d * β) := by
  rw [Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Fin.isValue, Matrix.of_apply]
  ring

/-- Core matrix-entry identity for Shimura Prop 3.34 — integer form, top-left.

For `g = !![a, b; N·c, d]` and `h = !![α, β; N·γ, δ]` in `M₂(ℤ)`,
the (0,0) entry of `adj(g) · h · g` equals
`a·d·α + N · (-a·b·γ + c·d·β - b·c·δ)`.

Parallel to `adj_mul_mul_entry_11_eq`, obtained by expanding the product. -/
lemma adj_mul_mul_entry_00_eq (N : ℤ) (a b c d α β γ δ : ℤ) :
    ((Matrix.adjugate !![a, b; N * c, d] *
        !![α, β; N * γ, δ]) * !![a, b; N * c, d]) 0 0 =
      a * d * α + N * (-(a * b * γ) + c * d * β - b * c * δ) := by
  rw [Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Fin.isValue, Matrix.of_apply]
  ring

/-! ### Rational-level identities via `g⁻¹ · h · g`

Converting the adjugate computation into a statement about the actual
matrix inverse. Over `ℚ`, `g⁻¹ = (1/det g) • adj g` when `det g ≠ 0`,
so `det g · (g⁻¹ * h * g) = adj g * h * g`. Cast the ℤ-identity along
that bridge. -/

/-- Bridge from `adj` to `g⁻¹` at an arbitrary entry: over a field, assuming
`det g ≠ 0`, we have `(g⁻¹ · h · g)ᵢⱼ · det g = (adj g · h · g)ᵢⱼ`. -/
private lemma inv_mul_mul_entry_smul_det {K : Type*} [Field K]
    (g h : Matrix (Fin 2) (Fin 2) K) (hdet : g.det ≠ 0) (i j : Fin 2) :
    (g⁻¹ * h * g) i j * g.det = (Matrix.adjugate g * h * g) i j := by
  have hinv : g⁻¹ = (g.det)⁻¹ • Matrix.adjugate g := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hinv]
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- Core matrix-entry lemma for Shimura Prop 3.34 — ℚ form, (1,1) entry.

For `g = !![a, b; N·c, d] ∈ M₂(ℤ)` with `det g ≠ 0`, and
`h = !![α, β; N·γ, δ] ∈ M₂(ℤ)` (both promoted to `M₂(ℚ)` through
the integer cast), the (1,1) entry of the rational conjugate `g⁻¹ · h · g`
satisfies
```
(g⁻¹ · h · g)₁₁ · det g = a·d·δ + N · (a·b·γ - b·c·α - c·d·β)
```
as an equation in ℚ. In particular `(g⁻¹ · h · g)₁₁ · det g ≡ a·d·δ (mod N)`
whenever the LHS is an integer.

This is the key identity for Shimura Proposition 3.34. -/
lemma matrix_fin_two_conj_entry_11_mod_eq
    (N : ℤ) (a b c d α β γ δ : ℤ)
    (hdet : (!![(a : ℚ), b; N * c, d]).det ≠ 0) :
    ((!![(a : ℚ), b; N * c, d])⁻¹ *
        !![(α : ℚ), β; N * γ, δ] * !![(a : ℚ), b; N * c, d]) 1 1 *
      (!![(a : ℚ), b; N * c, d]).det =
      (a : ℚ) * d * δ + N * (a * b * γ - b * c * α - c * d * β) := by
  rw [inv_mul_mul_entry_smul_det _ _ hdet, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Fin.isValue, Matrix.of_apply]
  ring

/-- Core matrix-entry lemma for Shimura Prop 3.34 — ℚ form, (0,0) entry.

Parallel to `matrix_fin_two_conj_entry_11_mod_eq`: for
`g = !![a, b; N·c, d]` with `det g ≠ 0`, and `h = !![α, β; N·γ, δ]`,
```
(g⁻¹ · h · g)₀₀ · det g = a·d·α + N · (-a·b·γ + c·d·β - b·c·δ)
```
over ℚ, so `(g⁻¹ · h · g)₀₀ · det g ≡ a·d·α (mod N)` when the LHS is
integer-valued. -/
lemma matrix_fin_two_conj_entry_00_mod_eq
    (N : ℤ) (a b c d α β γ δ : ℤ)
    (hdet : (!![(a : ℚ), b; N * c, d]).det ≠ 0) :
    ((!![(a : ℚ), b; N * c, d])⁻¹ *
        !![(α : ℚ), β; N * γ, δ] * !![(a : ℚ), b; N * c, d]) 0 0 *
      (!![(a : ℚ), b; N * c, d]).det =
      (a : ℚ) * d * α + N * (-(a * b * γ) + c * d * β - b * c * δ) := by
  rw [inv_mul_mul_entry_smul_det _ _ hdet, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Fin.isValue, Matrix.of_apply]
  ring

/-! ### Mod-`N` congruence corollaries

Packaging the identities as divisibility / congruence statements: after
subtracting the "diagonal part" `a·d·δ` (resp. `a·d·α`), the remainder
is an `N`-multiple. This is the form consumed by `Gamma0MapUnits`
preservation. -/

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

/-! ### Good-prime case — P334-B

We prove that conjugation by `g ∈ Δ₀(N)` with `gcd(det g, N) = 1` preserves
`Gamma0MapUnits`. The argument follows from the matrix-entry identity of
P334-A: modulo `N`, `(g⁻¹ h g)₁₁ · det g ≡ a·d·δ`, and `det g ≡ a·d (mod N)`,
so after dividing by `a·d` (invertible mod `N`) we get `(g⁻¹ h g)₁₁ ≡ δ`. -/

/-- Core arithmetic fact: if `det A ≡ a·d (mod N)` and `det A` is coprime to `N`,
then `a·d` is a unit mod `N`. Used to divide out the `a·d` factor in the mod-`N`
congruence from `matrix_fin_two_conj_entry_11_mod_eq`. -/
private lemma isUnit_ad_of_det_coprime {N : ℕ} (a b c d : ℤ)
    (hdet : Int.gcd (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det N = 1) :
    IsUnit ((a * d : ℤ) : ZMod N) := by
  -- Convert coprime to ZMod: the det and a*d differ by N*(b*c), so they agree mod N
  have hdetval : (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det = a * d - b * ((N : ℤ) * c) := by
    rw [Matrix.det_fin_two]
    simp
  have heq : ((a * d : ℤ) : ZMod N) =
      (((!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det : ℤ) : ZMod N) := by
    rw [hdetval]
    push_cast
    rw [show ((N : ZMod N)) = 0 from ZMod.natCast_self N]
    ring
  rw [heq, ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  exact_mod_cast hdet

/-- Mod-`N` version of the (1,1)-entry identity: after the rational equation
`(g⁻¹ h g)₁₁ · det g = a·d·δ + N·stuff` multiplies out over `ℤ` (via integrality
of the RHS), reducing mod `N` gives `h'₁₁ · det g ≡ a·d·δ (mod N)`. -/
private lemma entry_11_mul_det_congr_mod
    (N : ℕ) (a b c d α β γ δ : ℤ) (h'₁₁ : ℤ)
    (hdet : (!![(a : ℚ), b; (N : ℚ) * c, d]).det ≠ 0)
    (h_conj_11 :
      ((!![(a : ℚ), b; (N : ℚ) * c, d])⁻¹ *
          !![(α : ℚ), β; (N : ℚ) * γ, δ] * !![(a : ℚ), b; (N : ℚ) * c, d]) 1 1 =
        (h'₁₁ : ℚ)) :
    ((h'₁₁ * (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det : ℤ) : ZMod N) =
      ((a * d * δ : ℤ) : ZMod N) := by
  -- Start from P334-A identity, substitute h_conj_11, cast to ℤ then reduce mod N.
  have hdet_int : (!![(a : ℚ), b; ((N : ℤ) : ℚ) * c, d]).det ≠ 0 := by
    convert hdet using 2
  have hQ := matrix_fin_two_conj_entry_11_mod_eq (N : ℤ) a b c d α β γ δ hdet_int
  have hcastN : ((N : ℤ) : ℚ) = (N : ℚ) := by push_cast; rfl
  rw [hcastN] at hQ
  rw [h_conj_11] at hQ
  -- The rational det of the cast matrix equals the integer det, cast to ℚ
  have hdet_eq : (!![(a : ℚ), b; (N : ℚ) * c, d]).det =
      ((!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det : ℚ) := by
    simp only [Matrix.det_fin_two_of]; push_cast; ring
  rw [hdet_eq] at hQ
  -- hQ : (h'₁₁ : ℚ) * (detZ : ℚ) = (a*d*δ : ℤ : ℚ) + (N : ℤ : ℚ) * (stuff)
  -- Cast hQ from ℚ down to ℤ equality, then reduce mod N
  have hZ : h'₁₁ * (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det =
      a * d * δ + (N : ℤ) * (a * b * γ - b * c * α - c * d * β) := by
    exact_mod_cast hQ
  rw [hZ]
  push_cast
  ring_nf
  simp

/-- Descent from the `GL₂(ℚ)`-level conjugation equation to its `(1,1)` matrix
entry. Given `↑g = !![a, b; N·c, d]`, `mapGL ℚ hS = !![α, β; N·γ, δ]` and the
conjugation `mapGL ℚ h'S = g⁻¹ · mapGL ℚ hS · g`, the `(1,1)` entry of the
rational conjugate `g⁻¹ · (mapGL ℚ hS) · g` equals `(h'S)₁₁` (cast to `ℚ`). -/
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
    have h := congr_arg (fun X : GL (Fin 2) ℚ => (X : Matrix (Fin 2) (Fin 2) ℚ)) h'_conj
    simpa [Matrix.GeneralLinearGroup.coe_mul] using h
  have h_entry := congr_fun (congr_fun h_mat_eq 1) 1
  rw [hA_rat, hAh_rat] at h_entry
  rw [mapGL_coe_matrix] at h_entry
  simp only [algebraMap_int_eq] at h_entry
  exact h_entry.symm

/-- From the rational `(1,1)`-entry identity to the mod-`N` equality `h'₁₁ ≡ δ`.

Combining the integer congruence `h'₁₁ · det g ≡ a·d·δ (mod N)`
(`entry_11_mul_det_congr_mod`), the unit-ness of `a·d` mod `N`
(`isUnit_ad_of_det_coprime`, from `gcd(det g, N) = 1`) and `det g ≡ a·d (mod N)`,
cancel the `a·d` factor to obtain `h'₁₁ ≡ δ (mod N)`. -/
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
    simp only [Matrix.det_fin_two_of]
    push_cast
    rw [show ((N : ZMod N)) = 0 from ZMod.natCast_self N]
    ring
  have h_mod' : (h'₁₁ : ZMod N) * ((a * d : ℤ) : ZMod N) =
      ((a * d : ℤ) : ZMod N) * (δ : ZMod N) := by
    calc (h'₁₁ : ZMod N) * ((a * d : ℤ) : ZMod N)
        = (h'₁₁ : ZMod N) * ((detA : ℤ) : ZMod N) := by rw [hdetA_mod]
      _ = ((h'₁₁ * detA : ℤ) : ZMod N) := by push_cast; ring
      _ = ((a * d * δ : ℤ) : ZMod N) := h_mod
      _ = ((a * d : ℤ) : ZMod N) * (δ : ZMod N) := by push_cast; ring
  rw [mul_comm _ ((a * d : ℤ) : ZMod N)] at h_mod'
  exact had_unit.mul_left_cancel h_mod'

/-- Reshape of `g ∈ Δ₀(N)` into explicit integer entries: the rational matrix
`↑g` equals `!![a, b; N·c, d]` for integers `a, b, c, d` (with the `Δ₀(N)`
condition `N | g₁₀` realized as the `N·c` lower-left entry). -/
private lemma delta_elt_intCast_matrix_form {N : ℕ} [NeZero N]
    (g : (Gamma0_pair N).Δ) :
    ∃ a b c d : ℤ, (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(a : ℚ), (b : ℚ); (N : ℚ) * (c : ℚ), (d : ℚ)] := by
  obtain ⟨_, _, A, hA_eq, hAN, _⟩ := g.2
  obtain ⟨c, hc⟩ := hAN
  refine ⟨A 0 0, A 0 1, c, A 1 1, ?_⟩
  have hA_reshape : A = !![A 0 0, A 0 1; (N : ℤ) * c, A 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hc]
  rw [hA_eq, hA_reshape]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

/-- Reshape of `h ∈ Γ₀(N)` into explicit integer entries: `mapGL ℚ h` equals
`!![α, β; N·γ, δ]` for integers `α, β, γ, δ`, and the lower-right entry `δ`
agrees mod `N` with the underlying `SL₂(ℤ)` entry `h₁₁` (the value used by
`Gamma0Map`). -/
private lemma gamma0_elt_intCast_matrix_form {N : ℕ} (h : ↥(Gamma0 N)) :
    ∃ α β γ δ : ℤ, ((mapGL ℚ (h : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![(α : ℚ), (β : ℚ); (N : ℚ) * (γ : ℚ), (δ : ℚ)] ∧
      (δ : ZMod N) = ((h : SL(2, ℤ)).val 1 1 : ZMod N) := by
  set Ah : Matrix (Fin 2) (Fin 2) ℤ := (h : SL(2, ℤ)).val with hAh_def
  have hAh_N : (N : ℤ) ∣ Ah 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h.property)
  obtain ⟨γ, hγ⟩ := hAh_N
  refine ⟨Ah 0 0, Ah 0 1, γ, Ah 1 1, ?_, by rw [hAh_def]⟩
  have hAh_reshape : Ah = !![Ah 0 0, Ah 0 1; (N : ℤ) * γ, Ah 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hγ]
  rw [mapGL_coe_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, ← hAh_def, hγ]

/-- **P334-B**: For `g ∈ Δ₀(N)` with `gcd(det g, N) = 1`, `h h' ∈ Γ₀(N)` related by
`mapGL ℚ h' = g⁻¹ · mapGL ℚ h · g` in `GL₂(ℚ)`, the nebentypus character values
agree: `Gamma0MapUnits h' = Gamma0MapUnits h`.

This is the good-prime case of Shimura Proposition 3.34. The bad-prime case
(`gcd(det g, N) > 1`) is P334-C and may be skipped if all downstream applications
use coprime-determinant double cosets. -/
theorem Gamma0MapUnits_preserved_of_detCoprime {N : ℕ} [NeZero N]
    (g : (Gamma0_pair N).Δ)
    (h_det_coprime : ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        A.map (Int.cast : ℤ → ℚ) → Int.gcd A.det N = 1)
    (h h' : ↥(Gamma0 N))
    (h'_conj : (mapGL ℚ (h' : SL(2, ℤ)) : GL (Fin 2) ℚ) =
      (g : GL (Fin 2) ℚ)⁻¹ * mapGL ℚ (h : SL(2, ℤ)) * (g : GL (Fin 2) ℚ)) :
    Gamma0MapUnits h' = Gamma0MapUnits h := by
  -- Reshape g and h into explicit integer entries (Δ₀(N) / Γ₀(N) normal forms).
  obtain ⟨a, b, c, d, hA_rat⟩ := delta_elt_intCast_matrix_form g
  obtain ⟨α, β, γ, δ, hAh_rat, hδ_eq⟩ := gamma0_elt_intCast_matrix_form h
  set h'₁₁ : ℤ := (h' : SL(2, ℤ)).val 1 1
  -- det g ≠ 0 (g lies in GL₂) and gcd(det g, N) = 1 (from `h_det_coprime`).
  have hdet_ne : (!![(a : ℚ), (b : ℚ); (N : ℚ) * (c : ℚ), (d : ℚ)]).det ≠ 0 := by
    rw [← hA_rat]; exact Matrix.GeneralLinearGroup.det_ne_zero g.val
  have hdet_cop : Int.gcd (!![a, b; (N : ℤ) * c, d] : Matrix _ _ ℤ).det N = 1 := by
    apply h_det_coprime
    rw [hA_rat]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  -- Descend the GL-conjugation to the (1,1) entry, then cancel a·d mod N.
  have h_conj_11 := conj_matrix_entry_11_eq_intCast (g : GL (Fin 2) ℚ)
    (h : SL(2, ℤ)) (h' : SL(2, ℤ)) a b c d α β γ δ N hA_rat hAh_rat h'_conj
  have h'₁₁_eq_δ : (h'₁₁ : ZMod N) = (δ : ZMod N) :=
    conj_entry_11_intCast_eq_mod a b c d α β γ δ h'₁₁ hdet_ne hdet_cop h_conj_11
  -- Package as the `Gamma0Map` (hence `Gamma0MapUnits`) equality.
  have hGamma0Map : Gamma0Map N h' = Gamma0Map N h := by
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    show ((h' : SL(2, ℤ)).val 1 1 : ZMod N) = ((h : SL(2, ℤ)).val 1 1 : ZMod N)
    rw [← hδ_eq]; exact h'₁₁_eq_δ
  ext; rw [Gamma0MapUnits_val, Gamma0MapUnits_val, hGamma0Map]

end HeckeRing.GL2.Prop334
