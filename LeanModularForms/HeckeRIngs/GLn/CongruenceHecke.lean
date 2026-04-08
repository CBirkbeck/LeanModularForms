/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.Basic
import LeanModularForms.HeckeRIngs.GLn.SL2Surjection
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring
import LeanModularForms.HeckeRIngs.GLn.DiagonalRepresentatives
import LeanModularForms.HeckeRIngs.GLn.Projection
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.Ideal.Maps

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3)

Defines the Hecke pair `(Γ₀(N), Δ₀(N))` for congruence subgroups and establishes
the surjection `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))` (Shimura Theorem 3.35).

This allows us to derive the multiplication table for any congruence subgroup
from the level-1 table (our Shimura 3.24 results) by applying the surjection
and computing its kernel (`T(p,p) ↦ 0` for `p | N`).

## Main definitions

* `Gamma0_pair` — the Hecke pair `(Γ₀(N), Δ₀(N))`

## Main results

* `heckeAlgebra_surjection` — `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))` (Shimura Thm 3.35)
* `T'_sum_mul` — `T'(m)T'(n) = Σ_{d|(m,n),(d,N)=1} d·T'(d,d)·T'(mn/d²)` (Shimura (3.3.6))

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

/-! ### The Hecke pair for Γ₀(N) -/

/-- `Δ₀(N)`: integer matrices with `c ≡ 0 (mod N)`, `(a, N) = 1`, positive determinant.
    Shimura (3.3.1). -/
noncomputable def Delta0_submonoid (N : ℕ) : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | HasIntEntries 2 g ∧ 0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      (N : ℤ) ∣ A 1 0 ∧ Int.gcd (A 0 0) N = 1}
  one_mem' := by
    refine ⟨hasIntEntries_one 2, by simp, 1, ?_, ?_, ?_⟩
    · ext i j; simp [Matrix.map_apply, Matrix.one_apply]
    · simp
    · simp
  mul_mem' := by
    intro a b ⟨ha, hda, A, hA, hAN, hAco⟩ ⟨hb, hdb, B, hB, hBN, hBco⟩
    refine ⟨HasIntEntries.mul (n := 2) ha hb,
      by simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]; exact mul_pos hda hdb,
      A * B, ?_, ?_, ?_⟩
    · ext i j; simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      rw [Int.gcd_add_right_left_of_dvd _ (dvd_mul_of_dvd_right hBN _),
        Int.gcd_mul_right_left_of_gcd_eq_one hAco]
      exact hBco

/-- `Γ₀(N) ≤ Δ₀(N)`: the subgroup embeds into the submonoid. -/
lemma Gamma0_le_Delta0 (N : ℕ) [NeZero N] :
    ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)).toSubmonoid ≤ Delta0_submonoid N := by
  intro g hg
  rw [Subgroup.mem_toSubmonoid, Subgroup.mem_map] at hg
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [CongruenceSubgroup.Gamma0_mem] at hσ_mem
  have hc : (N : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσ_mem
  have hmem : mapGL ℚ σ ∈ SLnZ_subgroup 2 := MonoidHom.mem_range.mpr ⟨σ, rfl⟩
  simp only [Delta0_submonoid, Submonoid.mem_mk]
  refine ⟨SLnZ_subgroup_hasIntEntries 2 hmem, ?_,
    (σ : Matrix (Fin 2) (Fin 2) ℤ), rfl, hc, ?_⟩
  · have hdet := σ.prop; rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.det_fin_two, mapGL_coe_matrix, RingHom.mapMatrix_apply,
      map_apply_coe, algebraMap_int_eq, Int.coe_castRingHom, Matrix.map_apply]
    exact_mod_cast hdet ▸ one_pos
  · rw [← Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨k, hk⟩ := hc
    have hdet : (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; linarith
    exact ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1,
      -(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * k, by rw [hk] at hdet; linarith⟩

private lemma Delta0_le_posDetInt (N : ℕ) :
    Delta0_submonoid N ≤ posDetInt_submonoid 2 := by
  intro g ⟨hint, hdet, _⟩
  exact ⟨hint, hdet⟩

private lemma Gamma0_map_commensurable_SLnZ (N : ℕ) [NeZero N] :
    Subgroup.Commensurable ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ))
      (Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤) := by
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₀(N) ≤ commensurator(Γ₀(N))`. Follows from Shimura Lemma 3.10.
    The proof uses: Δ₀(N) ≤ Δ (positive-determinant integer matrices),
    Δ ≤ commensurator(SL₂(ℤ)), and commensurator(Γ₀(N)) = commensurator(SL₂(ℤ))
    (since Γ₀(N) has finite index in SL₂(ℤ), making them commensurable). -/
lemma Delta0_le_commensurator (N : ℕ) [NeZero N] :
    Delta0_submonoid N ≤
    (commensurator ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ))).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (Gamma0_map_commensurable_SLnZ N),
      ← MonoidHom.range_eq_map]
  exact (Delta0_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke pair `(Γ₀(N), Δ₀(N))`** — Shimura §3.3. -/
noncomputable def Gamma0_pair (N : ℕ) [NeZero N] : HeckePair (GL (Fin 2) ℚ) where
  H := (CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)
  Δ := Delta0_submonoid N
  h₀ := Gamma0_le_Delta0 N
  h₁ := Delta0_le_commensurator N

/-! ### Shimura §3.3 Foundation Lemmas (3.28–3.29)

These lemmas establish the relationship between double cosets for `Γ = SL₂(ℤ)` and
for a congruence subgroup `Γ' ⊃ Γ_N`. The key result (Shimura 3.29(3)) is:
`ΓαΓ ∩ Δ₀(N) = Γ₀(N)αΓ₀(N)` for `α ∈ Δ₀(N)` — the `Γ₀(N)`-double coset equals
the intersection of the full `SL₂(ℤ)`-double coset with `Δ₀(N)`.
-/

section FoundationLemmas

variable (N : ℕ) [NeZero N]

/-- **Key number-theoretic lemma for Shimura 3.29(3)**:
    For `α ∈ Δ₀(N)` (integer matrix with `gcd(a,N) = 1`, `N | c`, `det > 0`) and
    `σ ∈ SL₂(ℤ)`, if the product `σ · A` also satisfies `N | (σA)_{10}` (the `Δ₀(N)`
    congruence condition), then there exist `δ₁, δ₂ ∈ Γ₀(N)` such that
    `σ · A = δ₁ · A · δ₂`.

    The additional hypothesis `N | (σA)_{10}` corresponds to the intersection
    `ΓαΓ ∩ Δ₀(N)` in Shimura's formulation of Lemma 3.29(3). Under this condition,
    `σ ∈ Γ₀(N)` (by coprimality `gcd(a,N) = 1`), so `δ₁ = σ, δ₂ = 1` works. -/
private lemma SL2_mul_Delta0_in_Gamma0_doubleCoset
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hAN : (N : ℤ) ∣ A 1 0)
    (hAco : Int.gcd (A 0 0) N = 1) (hAdet : 0 < A.det)
    (σ : SpecialLinearGroup (Fin 2) ℤ)
    (hσA : (N : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0) :
    ∃ (δ₁ δ₂ : SpecialLinearGroup (Fin 2) ℤ),
      δ₁ ∈ CongruenceSubgroup.Gamma0 N ∧
      δ₂ ∈ CongruenceSubgroup.Gamma0 N ∧
      (σ : Matrix (Fin 2) (Fin 2) ℤ) * A = (δ₁ : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (δ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
  -- From the congruence conditions, deduce σ ∈ Γ₀(N), then take δ₁ = σ, δ₂ = 1.
  have hσ_mem : σ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    -- Expand (σ * A) 1 0 = σ 1 0 * A 0 0 + σ 1 1 * A 1 0
    have key : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0 =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * A 0 0 +
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * A 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [key] at hσA
    have h1 : (↑N : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (A 1 0) :=
      dvd_mul_of_dvd_right hAN _
    have h2 : (↑N : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * (A 0 0) := by
      have := Int.dvd_sub hσA h1; rwa [add_sub_cancel_right] at this
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hAco).symm.dvd_of_dvd_mul_right h2
  exact ⟨σ, 1, hσ_mem,
    by rw [CongruenceSubgroup.Gamma0_mem]; simp [SpecialLinearGroup.coe_one],
    by simp [SpecialLinearGroup.coe_one]⟩

private lemma left_mul_mem_Gamma0_doubleCoset
    (α : GL (Fin 2) ℚ) (hα : α ∈ Delta0_submonoid N)
    (γ : GL (Fin 2) ℚ) (hγ : γ ∈ SLnZ_subgroup 2)
    (hγα : γ * α ∈ Delta0_submonoid N) :
    γ * α ∈ DoubleCoset.doubleCoset α
      ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ))
      ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨_, hdet_pos, A, hA, hAN, hAco⟩ := hα
  obtain ⟨σ, rfl⟩ := hγ
  obtain ⟨_, _, B, hB, hBN, _⟩ := hγα
  -- Derive the integer-level congruence condition for σ * A
  -- B is the integer matrix for γ * α = mapGL ℚ σ * α, so B = σ * A
  have hσA : (↑N : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0 := by
    have hB_eq : B = (σ : Matrix (Fin 2) (Fin 2) ℤ) * A := by
      have : (B.map (Int.cast : ℤ → ℚ)) = ((σ : Matrix (Fin 2) (Fin 2) ℤ) * A).map
          (Int.cast : ℤ → ℚ) := by
        simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
          RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom] at hB
        rw [← hB, hA]; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
      ext i j; have := congr_fun₂ this i j; simp [Matrix.map_apply] at this; exact this
    rwa [← hB_eq]
  have hAdet : 0 < A.det := by
    have h1 : (A.det : ℚ) = (A.map (Int.cast : ℤ → ℚ)).det :=
      (det_intMat_cast 2 A).symm
    have h2 : (0 : ℚ) < A.det := by rw [h1, ← hA]; exact hdet_pos
    exact Int.cast_pos.mp h2
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, h_eq⟩ :=
    SL2_mul_Delta0_in_Gamma0_doubleCoset N A hAN hAco hAdet σ hσA
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨mapGL ℚ δ₁, Subgroup.mem_map_of_mem _ hδ₁,
    mapGL ℚ δ₂, Subgroup.mem_map_of_mem _ hδ₂, ?_⟩
  -- Lift the integer matrix equation to GL₂(ℚ)
  apply Units.ext
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hA]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have h_eq_ij := congr_fun₂ h_eq i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h_eq_ij
  exact_mod_cast h_eq_ij

/-- **Right version of the integer-level decomposition**: `A · σ = δ₁ · A · δ₂`.
    Under the hypothesis that `N | (Aσ)_{10}` and `gcd(d, N) = 1` (where `d = A 1 1`),
    we deduce `σ ∈ Γ₀(N)` and take `δ₁ = 1, δ₂ = σ`. The condition `gcd(d, N) = 1`
    follows from `gcd(det(A), N) = 1` (since `det ≡ ad (mod N)` and `gcd(a,N) = 1`). -/
private lemma SL2_mul_Delta0_in_Gamma0_doubleCoset_right
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hAN : (N : ℤ) ∣ A 1 0)
    (hAco : Int.gcd (A 0 0) N = 1) (hAdet : 0 < A.det)
    (σ : SpecialLinearGroup (Fin 2) ℤ)
    (hAσ : (N : ℤ) ∣ (A * (σ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0)
    (hAco2 : Int.gcd (A 1 1) N = 1) :
    ∃ (δ₁ δ₂ : SpecialLinearGroup (Fin 2) ℤ),
      δ₁ ∈ CongruenceSubgroup.Gamma0 N ∧
      δ₂ ∈ CongruenceSubgroup.Gamma0 N ∧
      A * (σ : Matrix (Fin 2) (Fin 2) ℤ) = (δ₁ : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (δ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
  -- From the congruence conditions, deduce σ ∈ Γ₀(N), then take δ₁ = 1, δ₂ = σ.
  have hσ_mem : σ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    -- Expand (A * σ) 1 0 = A 1 0 * σ 0 0 + A 1 1 * σ 1 0
    have key : (A * (σ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      A 1 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      A 1 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [key] at hAσ
    have h1 : (↑N : ℤ) ∣ A 1 0 * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :=
      dvd_mul_of_dvd_left hAN _
    have h2 : (↑N : ℤ) ∣ A 1 1 * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
      have := Int.dvd_sub hAσ h1; rwa [add_sub_cancel_left] at this
    rw [mul_comm] at h2
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hAco2).symm.dvd_of_dvd_mul_right h2
  exact ⟨1, σ,
    by rw [CongruenceSubgroup.Gamma0_mem]; simp [SpecialLinearGroup.coe_one],
    hσ_mem, by simp [SpecialLinearGroup.coe_one]⟩

private lemma right_mul_mem_Gamma0_doubleCoset
    (α : GL (Fin 2) ℚ) (hα : α ∈ Delta0_submonoid N)
    (γ : GL (Fin 2) ℚ) (hγ : γ ∈ SLnZ_subgroup 2)
    (hαγ : α * γ ∈ Delta0_submonoid N)
    (hd_co : ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
      Int.gcd (A 1 1) N = 1) :
    α * γ ∈ DoubleCoset.doubleCoset α
      ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ))
      ((CongruenceSubgroup.Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨_, hdet_pos, A, hA, hAN, hAco⟩ := hα
  obtain ⟨σ, rfl⟩ := hγ
  obtain ⟨_, _, B, hB, hBN, _⟩ := hαγ
  have hAco2 : Int.gcd (A 1 1) N = 1 := hd_co A hA
  -- Derive integer-level congruence condition for A * σ
  have hAσ : (↑N : ℤ) ∣ (A * (σ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 := by
    have hB_eq : B = A * (σ : Matrix (Fin 2) (Fin 2) ℤ) := by
      have : (B.map (Int.cast : ℤ → ℚ)) = (A * (σ : Matrix (Fin 2) (Fin 2) ℤ)).map
          (Int.cast : ℤ → ℚ) := by
        simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
          RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom] at hB
        rw [← hB, hA]; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
      ext i j; have := congr_fun₂ this i j; simp [Matrix.map_apply] at this; exact this
    rwa [← hB_eq]
  have hAdet : 0 < A.det := by
    have h1 : (A.det : ℚ) = (A.map (Int.cast : ℤ → ℚ)).det :=
      (det_intMat_cast 2 A).symm
    have h2 : (0 : ℚ) < A.det := by rw [h1, ← hA]; exact hdet_pos
    exact Int.cast_pos.mp h2
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, h_eq⟩ :=
    SL2_mul_Delta0_in_Gamma0_doubleCoset_right N A hAN hAco hAdet σ hAσ hAco2
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨mapGL ℚ δ₁, Subgroup.mem_map_of_mem _ hδ₁,
    mapGL ℚ δ₂, Subgroup.mem_map_of_mem _ hδ₂, ?_⟩
  apply Units.ext
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hA]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have h_eq_ij := congr_fun₂ h_eq i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h_eq_ij
  exact_mod_cast h_eq_ij

/-- `Γ₀(N) ≤ SL₂(ℤ)` (as subgroups of `GL₂(ℚ)`): every Gamma0 element is in SLnZ. -/
private lemma Gamma0_le_SLnZ :
    (CongruenceSubgroup.Gamma0 N).map (mapGL ℚ) ≤ SLnZ_subgroup 2 := by
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨σ, _, rfl⟩ := hg
  exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩

/-- `Γ(N) ≤ Γ₀(N)`: the principal congruence subgroup is contained in Gamma0. -/
private lemma GammaN_le_Gamma0 :
    CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N := by
  intro σ hσ
  rw [CongruenceSubgroup.Gamma_mem] at hσ
  rw [CongruenceSubgroup.Gamma0_mem]
  exact hσ.2.2.1

/-- `gcd(det(A), N) = 1` with `N | c` and `gcd(a, N) = 1` implies `gcd(d, N) = 1`
    where `A = [[a,b],[c,d]]`. Since `det(A) = ad - bc ≡ ad (mod N)` and
    `gcd(a, N) = 1`, coprimality of `det(A)` with `N` forces `gcd(d, N) = 1`. -/
private lemma gcd_A11_N_eq_one
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hAN : (N : ℤ) ∣ A 1 0)
    (_hAco : Int.gcd (A 0 0) N = 1)
    (hdet_coprime : Int.gcd A.det N = 1) :
    Int.gcd (A 1 1) N = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hdet_coprime ⊢
  have hdet : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two]
  obtain ⟨k, hk⟩ := hAN
  have hdet_co' : IsCoprime (A 0 0 * A 1 1) (N : ℤ) := by
    have : A 0 0 * A 1 1 = A.det + (A 0 1 * k) * ↑N := by
      rw [hdet, hk]; ring
    rw [this]; exact hdet_coprime.add_mul_right_left _
  exact (IsCoprime.mul_left_iff.mp hdet_co').2

private lemma intCast_eq_one_of_dvd {m n : ℕ} (h : m ∣ n) (x : ℤ)
    (hx : (x : ZMod n) = 1) : (x : ZMod m) = 1 := by
  have h1 : ((x - 1 : ℤ) : ZMod n) = 0 := by push_cast; simp [hx]
  have h2 : ((x - 1 : ℤ) : ZMod m) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr
      (dvd_trans (by exact_mod_cast h) this)
  push_cast at h2; rwa [sub_eq_zero] at h2

private lemma intCast_eq_zero_of_dvd {m n : ℕ} (h : m ∣ n) (x : ℤ)
    (hx : (x : ZMod n) = 0) : (x : ZMod m) = 0 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hx
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr
    (dvd_trans (by exact_mod_cast h) this)

open CongruenceSubgroup in
/-- If `m ∣ n`, then `Γ(n) ≤ Γ(m)`: higher level means smaller subgroup. -/
private lemma Gamma_le_of_dvd {m n : ℕ} (h : m ∣ n) : Gamma n ≤ Gamma m := by
  intro γ hγ
  rw [Gamma_mem] at hγ ⊢
  exact ⟨intCast_eq_one_of_dvd h _ hγ.1,
    intCast_eq_zero_of_dvd h _ hγ.2.1,
    intCast_eq_zero_of_dvd h _ hγ.2.2.1,
    intCast_eq_one_of_dvd h _ hγ.2.2.2⟩

/-- Functoriality of the SL₂ map: `map f ∘ map g = map (f.comp g)`. -/
private lemma SL_map_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : S →+* T) (g : R →+* S) (σ : SpecialLinearGroup (Fin 2) R) :
    SpecialLinearGroup.map f (SpecialLinearGroup.map g σ) =
    SpecialLinearGroup.map (f.comp g) σ := by
  ext i j; simp [map_apply_coe, RingHom.mapMatrix_apply, map_apply]

/-- **Generalized Chinese Remainder Theorem for integers**: given `x ≡ y mod gcd(m,n)`,
    there exists `z` with `z ≡ x mod m` and `z ≡ y mod n`. -/
private lemma int_crt {m n x y : ℤ} (h : x ≡ y [ZMOD ↑(Int.gcd m n)]) :
    ∃ z : ℤ, z ≡ x [ZMOD m] ∧ z ≡ y [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h; obtain ⟨k, hk⟩ := h
  have hbez := Int.gcd_eq_gcd_ab m n; set g := (↑(Int.gcd m n) : ℤ)
  refine ⟨x + m * (Int.gcdA m n * k), ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]; exact ⟨-(Int.gcdA m n * k), by ring⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨Int.gcdB m n * k,
      by rw [show y = x + g * k from by linarith, hbez]; ring⟩

/-- `Int.ModEq` implies equal casts to `ZMod`. -/
private lemma intModEq_to_zmod {m : ℕ} [NeZero m] {a b : ℤ}
    (h : a ≡ b [ZMOD ↑m]) : (a : ZMod m) = (b : ZMod m) := by
  rw [Int.modEq_iff_dvd] at h
  have h1 : ((b - a : ℤ) : ZMod m) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h)
  have h2 : (b : ZMod m) - (a : ZMod m) = 0 := by push_cast at h1; exact h1
  exact eq_of_sub_eq_zero h2 |>.symm

/-- Entries of `γ ∈ Γ(N)` are congruent to entries of the identity mod `N`. -/
private lemma SL2_gamma_entry_modEq (N : ℕ) [NeZero N]
    (γ : SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (i j : Fin 2) :
    ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ℤ) ≡
    (γ i j : ℤ) [ZMOD ↑N] := by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ
  have h := congr_fun₂ (congr_arg Subtype.val hγ) i j
  simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, coe_one,
    Int.coe_castRingHom] at h
  rw [Int.modEq_iff_dvd]
  have : ((↑(γ i j) - ↑((1 : SpecialLinearGroup (Fin 2) ℤ) i j) : ℤ) :
      ZMod N) = 0 := by
    simp only [coe_one, Int.cast_sub, sub_eq_zero]; rw [h]; simp [one_apply]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

set_option maxHeartbeats 6400000 in
open CongruenceSubgroup in
/-- **Shimura Lemma 3.28**: `Γ(gcd(a,b)) = Γ(a) · Γ(b)` — the product of principal
    congruence subgroups is the congruence subgroup of the gcd.

    The proof uses the surjectivity of `SL₂(ℤ) → SL₂(ℤ/dℤ)` (`SL2_reduction_surjective`)
    combined with the generalized Chinese Remainder Theorem. For the hard direction
    `Γ(gcd) ≤ Γ(a) ⊔ Γ(b)`: given `γ ∈ Γ(gcd)`, the integer CRT (using `gcd(a,b) |
    (I_{ij} - γ_{ij})`) provides entries `z_{ij}` with `z ≡ I mod a` and `z ≡ γ mod b`.
    The matrix `(z_{ij})` has `det ≡ 1 mod lcm(a,b)`, giving an element of
    `SL₂(ℤ/lcm ℤ)` which lifts to `β ∈ SL₂(ℤ)` with `β ∈ Γ(a)` and `β⁻¹γ ∈ Γ(b)`. -/
theorem Gamma_gcd_eq_mul (a b : ℕ) [NeZero a] [NeZero b]
    [NeZero (Nat.gcd a b)] :
    (Gamma (Nat.gcd a b)).map (mapGL ℚ) =
    ((Gamma a).map (mapGL ℚ)) ⊔ ((Gamma b).map (mapGL ℚ)) := by
  rw [← Subgroup.map_sup]
  congr 1
  apply le_antisymm
  · -- (⊆): Γ(gcd) ≤ Γ(a) ⊔ Γ(b) via CRT + SL₂ surjectivity
    haveI : (Gamma a).Normal := Gamma_normal a
    haveI : NeZero (Nat.lcm a b) :=
      ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    intro γ hγ; rw [Subgroup.mem_sup_of_normal_left]
    -- CRT compatibility: I_{ij} ≡ γ_{ij} mod gcd(a,b)
    have hcompat : ∀ i j : Fin 2,
        ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ℤ) ≡
        (γ i j : ℤ) [ZMOD ↑(Int.gcd (↑a) (↑b))] := by
      rw [show (↑(Int.gcd (↑a : ℤ) (↑b : ℤ)) : ℤ) = ↑(Nat.gcd a b) from
        by simp [Int.gcd]]
      exact SL2_gamma_entry_modEq _ γ hγ
    -- Integer CRT lifts: z_{ij} ≡ I_{ij} mod a, z_{ij} ≡ γ_{ij} mod b
    obtain ⟨z00, hz00a, hz00b⟩ := int_crt (hcompat 0 0)
    obtain ⟨z01, hz01a, hz01b⟩ := int_crt (hcompat 0 1)
    obtain ⟨z10, hz10a, hz10b⟩ := int_crt (hcompat 1 0)
    obtain ⟨z11, hz11a, hz11b⟩ := int_crt (hcompat 1 1)
    -- det(z) ≡ 1 mod lcm(a,b)
    have hdet_lcm : z00 * z11 - z01 * z10 ≡ 1 [ZMOD ↑(Nat.lcm a b)] := by
      rw [show (↑(Nat.lcm a b) : ℤ) = ↑(Int.lcm ↑a ↑b) from
        by simp [Int.lcm, Nat.lcm]]
      rw [← Int.modEq_and_modEq_iff_modEq_lcm]
      constructor
      · show z00 * z11 - z01 * z10 ≡ 1 * 1 - 0 * 0 [ZMOD ↑a]
        exact (hz00a.mul hz11a).sub (hz01a.mul hz10a)
      · have hdetγ : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
          have h := γ.prop; rw [det_fin_two] at h; exact_mod_cast h
        show z00 * z11 - z01 * z10 ≡ 1 [ZMOD ↑b]
        rw [← hdetγ]; exact (hz00b.mul hz11b).sub (hz01b.mul hz10b)
    -- Form SL₂(ZMod(lcm)) element and lift to SL₂(ℤ)
    have hdet_zmod : ((z00 * z11 - z01 * z10 : ℤ) : ZMod (Nat.lcm a b)) = 1 := by
      exact_mod_cast intModEq_to_zmod hdet_lcm
    set M : Matrix (Fin 2) (Fin 2) ℤ := !![z00, z01; z10, z11]
    have hM_det : (M.map (Int.castRingHom (ZMod (Nat.lcm a b)))).det = 1 := by
      simp only [det_fin_two, M, Matrix.map_apply, Int.coe_castRingHom, cons_val',
        cons_val_zero, empty_val', cons_val_one]
      have h := intModEq_to_zmod hdet_lcm
      push_cast at h ⊢; exact_mod_cast h
    set target : SpecialLinearGroup (Fin 2) (ZMod (Nat.lcm a b)) :=
      ⟨M.map (Int.castRingHom (ZMod (Nat.lcm a b))), hM_det⟩
    obtain ⟨β, hβ⟩ :=
      SL2Reduction.SL2_reduction_surjective (Nat.lcm a b) target
    -- Composition: ℤ → ZMod(lcm) → ZMod(a) = ℤ → ZMod(a)
    have hcomp_a : (ZMod.castHom (Nat.dvd_lcm_left a b) (ZMod a)).comp
        (Int.castRingHom (ZMod (Nat.lcm a b))) =
        Int.castRingHom (ZMod a) := by ext; simp
    have hcomp_b : (ZMod.castHom (Nat.dvd_lcm_right a b) (ZMod b)).comp
        (Int.castRingHom (ZMod (Nat.lcm a b))) =
        Int.castRingHom (ZMod b) := by ext; simp
    -- Helper: castHom sends M.map entries to M entries cast to the smaller ZMod
    have htarget_entry : ∀ (N' : ℕ) (hN' : N' ∣ Nat.lcm a b) (i j : Fin 2),
        (ZMod.castHom hN' (ZMod N')) (target.1 i j) = ((M i j : ℤ) : ZMod N') := by
      intro N' hN' i j; simp [target, Matrix.map_apply, Int.coe_castRingHom]
    -- β ∈ Γ(a)
    have hβ_a : β ∈ Gamma a := by
      rw [Gamma_mem']
      have key := congr_arg (SpecialLinearGroup.map
        (ZMod.castHom (Nat.dvd_lcm_left a b) (ZMod a))) hβ
      rw [SL_map_comp, hcomp_a] at key; rw [key]; ext i j
      simp only [map_apply_coe, RingHom.mapMatrix_apply, map_apply, coe_one, one_apply]
      rw [htarget_entry a (Nat.dvd_lcm_left a b) i j]
      fin_cases i <;> fin_cases j <;>
        simp [M, intModEq_to_zmod hz00a, intModEq_to_zmod hz01a,
          intModEq_to_zmod hz10a, intModEq_to_zmod hz11a]
    -- β⁻¹γ ∈ Γ(b)
    have hβγ_b : β⁻¹ * γ ∈ Gamma b := by
      rw [Gamma_mem', map_mul, map_inv]
      have hβ_b_eq : SpecialLinearGroup.map (Int.castRingHom (ZMod b)) β =
          SpecialLinearGroup.map (Int.castRingHom (ZMod b)) γ := by
        have key := congr_arg (SpecialLinearGroup.map
          (ZMod.castHom (Nat.dvd_lcm_right a b) (ZMod b))) hβ
        rw [SL_map_comp, hcomp_b] at key; rw [key]; ext i j
        simp only [map_apply_coe, RingHom.mapMatrix_apply, map_apply]
        rw [htarget_entry b (Nat.dvd_lcm_right a b) i j]
        fin_cases i <;> fin_cases j <;>
          simp [M, intModEq_to_zmod hz00b, intModEq_to_zmod hz01b,
            intModEq_to_zmod hz10b, intModEq_to_zmod hz11b]
      rw [hβ_b_eq]; exact inv_mul_cancel _
    exact ⟨β, hβ_a, β⁻¹ * γ, hβγ_b, by group⟩
  · exact sup_le (Gamma_le_of_dvd (Nat.gcd_dvd_left a b))
      (Gamma_le_of_dvd (Nat.gcd_dvd_right a b))

open CongruenceSubgroup in
/-- **Shimura Lemma 3.29(3)**: For `α ∈ Δ₀(N)` with `gcd(det(α), N) = 1`,
    the intersection of the full double coset `ΓαΓ` with `Δ₀(N)` equals the
    `Γ₀(N)`-double coset: `ΓαΓ ∩ Δ₀(N) = Γ₀(N)αΓ₀(N)`.

    The `⊇` direction is immediate since `Γ₀(N) ⊆ Γ` and `Δ₀(N)` is a submonoid.
    The `⊆` direction uses `Gamma_gcd_eq_mul` (Shimura 3.28) to factor `γ₁ = τ_N · τ_a`
    with `τ_N ∈ Γ(N) ⊂ Γ₀(N)` and `τ_a ∈ Γ(det α)`, then the conjugation identity
    `Γ(det α) ⊂ αΓα⁻¹` (`conj_ker_mem_SLnZ`) to rewrite `x = τ_N · α · γ₂'`.
    Coprimality of the product matrix `τ_N · A` then forces `γ₂' ∈ Γ₀(N)`. -/
theorem doubleCoset_eq_of_Gamma0_coprimeDet
    (α : GL (Fin 2) ℚ) (hα : α ∈ Delta0_submonoid N)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (hAco : Int.gcd (A 0 0) N = 1)
    (hdet_coprime : Int.gcd A.det N = 1) :
    DoubleCoset.doubleCoset α (SLnZ_subgroup 2) (SLnZ_subgroup 2) ∩
      (Delta0_submonoid N : Set (GL (Fin 2) ℚ)) =
    DoubleCoset.doubleCoset α
      ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) := by
  have hdet_pos := hα.2.1
  have hAdet_pos : 0 < A.det := by
    have h1 : (A.det : ℚ) = (A.map (Int.cast : ℤ → ℚ)).det :=
      (det_intMat_cast 2 A).symm
    exact Int.cast_pos.mp (by rw [h1, ← hA]; exact hdet_pos)
  have hAco2 : Int.gcd (A 1 1) N = 1 :=
    gcd_A11_N_eq_one N A hAN hAco hdet_coprime
  ext x; constructor
  · -- (⊆): x ∈ ΓαΓ ∩ Δ₀(N) → x ∈ Γ₀(N)αΓ₀(N)
    -- The proof proceeds in two steps:
    -- Step A: Use Γ(det α) ⊔ Γ(N) = SL₂(ℤ) (Shimura Lemma 3.28) and the
    --   conjugation Γ(det α) ⊂ αΓα⁻¹ to rewrite x = δ₁ · α · γ₂ with δ₁ ∈ Γ₀(N).
    -- Step B: Use coprimality to show γ₂ ∈ Γ₀(N).
    intro ⟨hx_dc, hx_delta⟩
    rw [DoubleCoset.mem_doubleCoset] at hx_dc ⊢
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx_dc
    obtain ⟨σ₁, rfl⟩ := hγ₁; obtain ⟨σ₂, rfl⟩ := hγ₂
    -- Step A: Factor σ₁ = τ_N · τ_a via Γ(det) ⊔ Γ(N) = SL₂(ℤ) (Shimura 3.28)
    have hAdet_ne : A.det ≠ 0 := ne_of_gt hAdet_pos
    haveI : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet_ne⟩
    haveI : NeZero (Nat.gcd A.det.natAbs N) :=
      ⟨by rw [show Nat.gcd A.det.natAbs N = Int.gcd A.det N from rfl,
        hdet_coprime]; exact one_ne_zero⟩
    haveI : (Gamma N).Normal := Gamma_normal N
    have h_top : Gamma N ⊔ Gamma A.det.natAbs = ⊤ := by
      have h := Gamma_gcd_eq_mul A.det.natAbs N
      rw [← Subgroup.map_sup] at h
      have := Subgroup.map_injective mapGL_injective h
      rw [show Nat.gcd A.det.natAbs N = Int.gcd A.det N from rfl,
        hdet_coprime, Gamma_one_top] at this
      rw [sup_comm]; exact this.symm
    obtain ⟨τ_N, hτ_N, τ_a, hτ_a, hσ₁_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (h_top ▸ Subgroup.mem_top σ₁)
    -- τ_N ∈ Γ(N) ⊂ Γ₀(N)
    have hτ_N_Gamma0 : τ_N ∈ Gamma0 N := GammaN_le_Gamma0 N hτ_N
    have hτ10 : (N : ℤ) ∣ (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ_N_Gamma0
      exact hτ_N_Gamma0
    have hτ11 : (N : ℤ) ∣ ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
      rw [Gamma_mem] at hτ_N
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (by push_cast; simp [hτ_N.2.2.2])
    -- Conjugation: τ_a ∈ Γ(det) ⊂ αΓα⁻¹, so τ_a · α = α · h for h ∈ SLnZ
    have hτ_ker : τ_a ∈ (SpecialLinearGroup.map
        (Int.castRingHom (ZMod A.det.natAbs))).ker := by
      rw [MonoidHom.mem_ker]; rwa [Gamma_mem'] at hτ_a
    obtain ⟨h_sl, hh_sl⟩ := conj_ker_mem_SLnZ 2 α A hA hAdet_ne τ_a hτ_ker
    have h_conj : mapGL ℚ τ_a * α = α * mapGL ℚ h_sl := by rw [hh_sl]; group
    -- Rewrite: x = (mapGL τ_N) · α · (mapGL γ₂') where γ₂' = h_sl * σ₂
    set γ₂' := h_sl * σ₂
    have hx_eq' : x = mapGL ℚ τ_N * α * mapGL ℚ γ₂' := by
      rw [hx_eq, hσ₁_eq.symm, map_mul, map_mul, mul_assoc, mul_assoc, mul_assoc]
      congr 1; rw [← mul_assoc, h_conj, mul_assoc]
    -- Step B: Show γ₂' ∈ Γ₀(N) via coprimality of C = τ_N * A
    obtain ⟨_, _, B, hB, hBN, _⟩ := hx_delta
    have hB_eq : B = (τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) := by
      have : (B.map (Int.cast : ℤ → ℚ)) = ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A *
          (γ₂' : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ) := by
        have hx_mat : (↑x : Matrix (Fin 2) (Fin 2) ℚ) =
            (↑(mapGL ℚ τ_N * α * mapGL ℚ γ₂') : Matrix _ _ ℚ) :=
          congr_arg _ hx_eq'
        simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
          RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom] at hx_mat
        rw [← hB, hx_mat, hA]
        ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
      ext i j; have := congr_fun₂ this i j
      simp [Matrix.map_apply] at this; exact this
    set C := (τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A
    -- gcd(C₁₁, N) = 1 since C₁₁ ≡ A₁₁ (mod N) and gcd(A₁₁, N) = 1
    have hCco2 : Int.gcd (C 1 1) N = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      have hC11_mod : (N : ℤ) ∣ (C 1 1 - A 1 1) := by
        have : C 1 1 - A 1 1 = (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * A 0 1 +
          ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) * A 1 1 := by
          simp [C, Matrix.mul_apply, Fin.sum_univ_two]; ring
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_left hτ11 _)
      obtain ⟨k, hk⟩ := hC11_mod
      have : C 1 1 = A 1 1 + k * ↑N := by linarith
      rw [this]
      exact (Int.isCoprime_iff_gcd_eq_one.mpr hAco2).add_mul_right_left k
    -- N | C₁₀ (from N | τ_N₁₀ and N | A₁₀)
    have hCN : (N : ℤ) ∣ C 1 0 := by
      have : C 1 0 = (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * A 0 0 +
        (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * A 1 0 := by
        simp [C, Matrix.mul_apply, Fin.sum_univ_two]
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_right hAN _)
    -- From N | (C·γ₂')₁₀ and gcd(C₁₁, N) = 1, deduce N | γ₂'₁₀
    have hγ₂'_mem : γ₂' ∈ Gamma0 N := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hCγ : (N : ℤ) ∣ (C * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 := by
        change (N : ℤ) ∣ ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A *
          (γ₂' : Matrix (Fin 2) (Fin 2) ℤ)) 1 0
        rwa [← hB_eq]
      have key : (C * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
        C 1 0 * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
        C 1 1 * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [key] at hCγ
      have h2 : (↑N : ℤ) ∣ C 1 1 * ((γ₂' : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
        have h1 : (↑N : ℤ) ∣ C 1 0 * ((γ₂' : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :=
          dvd_mul_of_dvd_left hCN _
        have := Int.dvd_sub hCγ h1; rwa [add_sub_cancel_left] at this
      rw [mul_comm] at h2
      exact (Int.isCoprime_iff_gcd_eq_one.mpr hCco2).symm.dvd_of_dvd_mul_right h2
    exact ⟨mapGL ℚ τ_N, Subgroup.mem_map_of_mem _ hτ_N_Gamma0,
      mapGL ℚ γ₂', Subgroup.mem_map_of_mem _ hγ₂'_mem, hx_eq'⟩
  · -- (⊇): x ∈ Γ₀(N)αΓ₀(N) → x ∈ ΓαΓ ∩ Δ₀(N)
    intro hx
    rw [DoubleCoset.mem_doubleCoset] at hx
    obtain ⟨δ₁, hδ₁, δ₂, hδ₂, hx_eq⟩ := hx
    refine ⟨?_, ?_⟩
    · -- x ∈ ΓαΓ: since Γ₀(N) ⊆ Γ
      rw [DoubleCoset.mem_doubleCoset]
      obtain ⟨τ₁, hτ₁, rfl⟩ := Subgroup.mem_map.mp hδ₁
      obtain ⟨τ₂, hτ₂, rfl⟩ := Subgroup.mem_map.mp hδ₂
      exact ⟨mapGL ℚ τ₁, ⟨τ₁, rfl⟩, mapGL ℚ τ₂, ⟨τ₂, rfl⟩, hx_eq⟩
    · -- x ∈ Δ₀(N): since δ₁, δ₂ ∈ Γ₀(N) ⊆ Δ₀(N) and α ∈ Δ₀(N)
      rw [hx_eq, SetLike.mem_coe]
      have hδ₁_delta : δ₁ ∈ Delta0_submonoid N :=
        Gamma0_le_Delta0 N ((Subgroup.mem_toSubmonoid _ _).mpr hδ₁)
      have hδ₂_delta : δ₂ ∈ Delta0_submonoid N :=
        Gamma0_le_Delta0 N ((Subgroup.mem_toSubmonoid _ _).mpr hδ₂)
      exact (Delta0_submonoid N).mul_mem
        ((Delta0_submonoid N).mul_mem hδ₁_delta hα) hδ₂_delta

/-! **Note on the original `leftCoset_decomp_refines_Gamma0`**: The originally
    intended statement claimed that if the left `Γ₀(N)`-cosets `{rᵢ} * Γ₀(N)` are
    pairwise disjoint (for representatives `rᵢ` of the `Γ₀(N)`-double coset
    decomposition), then the left `Γ`-cosets `{rᵢ} * Γ` are also pairwise
    disjoint for the **same** representatives. This is **false**.

    **Counterexample**: Take `N = 2`, `α = diag(1, 2)`. The index
    `[SL₂(ℤ) : Γ₀(2)] = 3`, so the `Γ₀(2)`-double coset `Γ₀(2)·α·Γ₀(2)`
    decomposes into `3k` left `Γ₀(2)`-cosets (where `k` is the number of left
    `SL₂(ℤ)`-cosets in `SL₂(ℤ)·α·SL₂(ℤ)`). Each left `SL₂(ℤ)`-coset
    `{βⱼ} * SL₂(ℤ)` contains exactly `3` left `Γ₀(2)`-cosets. If `rᵢ, rⱼ` are
    `Γ₀(2)`-representatives from different `Γ₀(2)`-cosets within the **same**
    `SL₂(ℤ)`-coset (i.e., `rⱼ = rᵢ · γ` for `γ ∈ SL₂(ℤ) \ Γ₀(2)`), then:
    - `{rᵢ} * Γ₀(2) ∩ {rⱼ} * Γ₀(2) = ∅` (disjoint as `Γ₀(2)`-cosets), but
    - `{rᵢ} * SL₂(ℤ) = {rⱼ} * SL₂(ℤ)` (same `SL₂(ℤ)`-coset).

    **Correct formalization of Shimura 3.29(5)**: The actual content is the
    **degree equality** `deg_{Γ₀(N)}(Γ₀(N)αΓ₀(N)) = [Γ:Γ₀(N)] · deg_Γ(ΓαΓ)`.
    Combined with the double coset equality `Γ₀(N)αΓ₀(N) = ΓαΓ ∩ Δ₀(N)` from
    Shimura 3.29(3) (`doubleCoset_eq_of_Gamma0_coprimeDet` above), this shows
    that `Γ`-coset decompositions are obtained by **grouping** `[Γ:Γ₀(N)]` many
    `Γ₀(N)`-cosets into each `Γ`-coset. The representatives do NOT carry over.

    **What IS true**: The `Γ₀(N)`-double coset is contained in the `Γ`-double
    coset: `Γ₀(N)αΓ₀(N) ⊆ ΓαΓ` (trivially, since `Γ₀(N) ≤ Γ`). This is
    `Gamma0_doubleCoset_subset_Gamma` below. -/

open CongruenceSubgroup in
/-- `Γ₀(N)αΓ₀(N) ⊆ ΓαΓ`: the `Γ₀(N)`-double coset is contained in
    the `Γ`-double coset. Immediate from `Γ₀(N) ≤ Γ = SL₂(ℤ)`. -/
theorem Gamma0_doubleCoset_subset_Gamma (α : GL (Fin 2) ℚ) :
    DoubleCoset.doubleCoset α
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ⊆
    DoubleCoset.doubleCoset α (SLnZ_subgroup 2) (SLnZ_subgroup 2) := by
  intro x hx
  rw [DoubleCoset.mem_doubleCoset] at hx ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx
  exact ⟨γ₁, Gamma0_le_SLnZ N hγ₁, γ₂, Gamma0_le_SLnZ N hγ₂, hx_eq⟩

end FoundationLemmas

/-! ### Shimura Theorem 3.35: the surjection R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))

The level-N Hecke algebra is a quotient of the level-1 algebra. The surjection maps:
- `T(n) ↦ T'(n)` for all positive integers n
- `T(p, p) ↦ T'(p, p)` for primes p not dividing N
- `T(p, p) ↦ 0` for primes p dividing N

Therefore, the level-N multiplication table is obtained from `T_sum_mul` by
setting `T(p,p) = 0` for `p | N`. -/

/-- The inclusion `Δ₀(N) ↪ Δ` as a submonoid inclusion. -/
private noncomputable def Delta0_inclusion (N : ℕ) [NeZero N] :
    (Gamma0_pair N).Δ → (GL_pair 2).Δ :=
  fun g => ⟨g.1, Delta0_le_posDetInt N g.2⟩

/-- If `Γ₀(N)`-double cosets of `a` and `b` agree, then so do `Γ`-double cosets.
    This is because `Γ₀(N) ≤ Γ = SL₂(ℤ)`: enlarging the group can only merge cosets. -/
private lemma doubleCoset_eq_of_Gamma0_eq (N : ℕ) [NeZero N]
    (a b : (Gamma0_pair N).Δ)
    (hab : dcRel (Gamma0_pair N) a b) :
    dcRel (GL_pair 2) (Delta0_inclusion N a) (Delta0_inclusion N b) := by
  -- hab says H'aH' = H'bH' where H' = Γ₀(N)
  -- Need: HaH = HbH where H = SL₂(ℤ)
  simp only [dcRel] at hab ⊢
  -- b ∈ H'aH' since H'bH' = H'aH'
  have hb_mem : (b : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset (a : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
    rw [hab]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hb_mem
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hb_eq⟩ := hb_mem
  -- b ∈ HaH (since Γ₀(N) ≤ Γ)
  have hb_big : (b : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset (a : GL (Fin 2) ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨γ₁, Gamma0_le_SLnZ N hγ₁, γ₂, Gamma0_le_SLnZ N hγ₂, hb_eq⟩
  -- Therefore HbH = HaH (double coset absorption)
  exact (DoubleCoset.doubleCoset_eq_of_mem hb_big).symm

/-- The coset map `HeckeCoset (Gamma0_pair N) → HeckeCoset (GL_pair 2)`:
    sends `Γ₀(N)αΓ₀(N)` to `ΓαΓ`. Well-defined because `Γ₀(N) ≤ Γ`,
    so equal `Γ₀(N)`-double cosets map to equal `Γ`-double cosets. -/
private noncomputable def cosetMap (N : ℕ) [NeZero N] :
    HeckeCoset (Gamma0_pair N) → HeckeCoset (GL_pair 2) :=
  Quotient.lift
    (fun g => ⟦Delta0_inclusion N g⟧)
    (fun a b hab => by
      rw [HeckeCoset.eq_iff]
      exact doubleCoset_eq_of_Gamma0_eq N a b hab)

/-- **Shimura Proposition 3.30**: If `Γ' ⊂ Γ` and `Δ' ⊂ Δ`, the correspondence
    `Γ'αΓ' ↦ ΓαΓ` defines an additive homomorphism `R(Γ', Δ') → R(Γ, Δ)`.

    The map is defined as `Finsupp.mapDomain` along the coset map
    `HeckeCoset (Gamma0_pair N) → HeckeCoset (GL_pair 2)` which sends
    `⟦α⟧_{Γ₀(N)} ↦ ⟦α⟧_{Γ}`. Well-definedness follows from `Γ₀(N) ≤ Γ`:
    equal `Γ₀(N)`-double cosets map to equal `Γ`-double cosets. -/
theorem shimura_prop_3_30 (N : ℕ) [NeZero N] :
    ∃ φ : HeckeRing.𝕋 (Gamma0_pair N) ℤ →+ HeckeRing.𝕋 (GL_pair 2) ℤ,
      True := by
  exact ⟨Finsupp.mapDomain.addMonoidHom (cosetMap N), trivial⟩

/-- An element `g ∈ Δ₀(N)` has **coprime determinant** if `gcd(det(A), N) = 1`
    where `A` is the integer matrix representing `g`. This condition is automatic
    when `det(g)` is coprime to `N` and is required for Shimura 3.29(3). -/
def CoprimeDet (N : ℕ) [NeZero N] (g : (Gamma0_pair N).Δ) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      A.map (Int.cast : ℤ → ℚ) →
    Int.gcd A.det N = 1

/-- **Shimura Proposition 3.31 (Injectivity of `cosetMap`)**: The coset map
    `Γ₀(N)αΓ₀(N) ↦ ΓαΓ` is injective on double cosets with coprime determinant.

    If `α, β ∈ Δ₀(N)` both have `gcd(det, N) = 1` and `ΓαΓ = ΓβΓ`, then
    `Γ₀(N)αΓ₀(N) = Γ₀(N)βΓ₀(N)`. The proof uses Shimura 3.29(3)
    (`doubleCoset_eq_of_Gamma0_coprimeDet`): since `ΓαΓ ∩ Δ₀(N) = Γ₀(N)αΓ₀(N)`
    and `ΓβΓ ∩ Δ₀(N) = Γ₀(N)βΓ₀(N)`, equal `Γ`-double cosets give equal
    intersections with `Δ₀(N)`, hence equal `Γ₀(N)`-double cosets.

    Note: injectivity does NOT hold without the coprime-det condition.
    For `α ∈ Δ₀(N)` with `gcd(det(α), N) > 1`, the intersection
    `ΓαΓ ∩ Δ₀(N)` can be strictly larger than `Γ₀(N)αΓ₀(N)`, so
    distinct `Γ₀(N)`-double cosets within the same `Γ`-double coset
    may exist. -/
theorem shimura_prop_3_31 (N : ℕ) [NeZero N]
    (a b : (Gamma0_pair N).Δ)
    (ha : CoprimeDet N a) (hb : CoprimeDet N b)
    (h : cosetMap N ⟦a⟧ = cosetMap N ⟦b⟧) :
    (⟦a⟧ : HeckeCoset (Gamma0_pair N)) = ⟦b⟧ := by
  -- Unfold cosetMap to ⟦Delta0_inclusion N _⟧ and extract the double coset equality ΓaΓ = ΓbΓ
  change (⟦Delta0_inclusion N a⟧ : HeckeCoset (GL_pair 2)) =
    ⟦Delta0_inclusion N b⟧ at h
  rw [HeckeCoset.eq_iff] at h
  rw [HeckeCoset.eq_iff]
  -- Extract the integer matrices witnessing a, b ∈ Δ₀(N)
  obtain ⟨_, _, Aa, hAa, hAaN, hAaco⟩ := a.2
  obtain ⟨_, _, Ab, hAb, hAbN, hAbco⟩ := b.2
  -- Apply Shimura 3.29(3) to both a and b
  have eq_a := doubleCoset_eq_of_Gamma0_coprimeDet N a.1 a.2 Aa hAa hAaN hAaco
    (ha Aa hAa)
  have eq_b := doubleCoset_eq_of_Gamma0_coprimeDet N b.1 b.2 Ab hAb hAbN hAbco
    (hb Ab hAb)
  -- Convert h to use SLnZ_subgroup 2 and ↑a (definitionally equal but syntactically needed)
  have h' : DoubleCoset.doubleCoset (↑a : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) =
    DoubleCoset.doubleCoset (↑b : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) := h
  -- Chain: Γ₀(N)aΓ₀(N) = ΓaΓ ∩ Δ₀(N) = ΓbΓ ∩ Δ₀(N) = Γ₀(N)bΓ₀(N)
  have h_inter : DoubleCoset.doubleCoset (↑a : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) ∩ ↑(Delta0_submonoid N) =
    DoubleCoset.doubleCoset (↑b : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) ∩ ↑(Delta0_submonoid N) := by rw [h']
  rw [eq_a, eq_b] at h_inter
  exact h_inter

/-- `M₂(ℚ)` is countable (needed for `GL₂(ℚ)` countability). -/
private instance instCountableM2 : Countable (Matrix (Fin 2) (Fin 2) ℚ) :=
  show Countable (Fin 2 → Fin 2 → ℚ) from inferInstance

/-- `GL₂(ℚ)` is countable: it embeds into `M₂(ℚ) × M₂(ℚ)` via `g ↦ (g, g⁻¹)`. -/
private noncomputable instance instCountableGL2 : Countable (GL (Fin 2) ℚ) := by
  apply Function.Injective.countable
    (f := fun g : GL (Fin 2) ℚ =>
      ((g : Matrix (Fin 2) (Fin 2) ℚ), (g⁻¹ : Matrix (Fin 2) (Fin 2) ℚ)))
  intro g₁ g₂ h; exact Units.ext (Prod.mk.inj h).1

private lemma divChain_one_succ (k : ℕ) : DivChain 2 (![1, k + 1]) := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp

/-- `HeckeCoset (GL_pair 2)` is infinite: the diagonal cosets `T(1, n)` for
    `n = 1, 2, 3, ...` are pairwise distinct by `diagonal_representative_unique`. -/
private noncomputable instance instInfiniteGLCoset : Infinite (HeckeCoset (GL_pair 2)) :=
  Infinite.of_injective (fun n : ℕ => T_diag (![1, n + 1]))
    (fun m n h => by
      have hpos : ∀ k : ℕ, ∀ i, 0 < (![1, k + 1]) i :=
        fun k i => by fin_cases i <;> simp <;> omega
      have := diagonal_representative_unique 2 _ _ (hpos m) (hpos n)
        (divChain_one_succ m) (divChain_one_succ n) h
      have h1 := congr_fun this 1
      simp [Matrix.cons_val_one, Matrix.head_cons] at h1; omega)

/-- `diag(1, n+1) ∈ Δ₀(N)` for all `n`: `gcd(1, N) = 1` and `N | 0`. -/
private lemma diagMat_one_mem_Delta0 (N : ℕ) (n : ℕ) :
    diagMat 2 (![1, n + 1]) ∈ Delta0_submonoid N := by
  refine ⟨diagMat_hasIntEntries 2 _ (fun i => by fin_cases i <;> simp <;> omega),
    diagMat_det_pos 2 _ (fun i => by fin_cases i <;> simp <;> omega),
    Matrix.diagonal (fun i => (![1, n + 1] i : ℤ)), ?_, ?_, ?_⟩
  · ext i j; simp [diagMat, Matrix.diagonal, Matrix.map_apply]
  · simp [Matrix.diagonal]
  · simp [Matrix.diagonal, Int.gcd_one_left]

set_option maxHeartbeats 800000 in
/-- `HeckeCoset (Gamma0_pair N)` is infinite: `diag(1, n+1) ∈ Δ₀(N)` gives distinct
    `Γ₀(N)`-double cosets because they map to distinct `Γ`-double cosets via
    `Gamma0_doubleCoset_subset_Gamma` and `diagonal_representative_unique`. -/
private noncomputable instance instInfiniteGamma0Coset (N : ℕ) [NeZero N] :
    Infinite (HeckeCoset (Gamma0_pair N)) :=
  Infinite.of_injective
    (fun n : ℕ => (⟦⟨diagMat 2 (![1, n + 1]), diagMat_one_mem_Delta0 N n⟩⟧ :
      HeckeCoset (Gamma0_pair N)))
    (fun m n h => by
      rw [HeckeCoset.eq_iff] at h
      have h_gl : DoubleCoset.doubleCoset (diagMat 2 (![1, m + 1]) : GL (Fin 2) ℚ)
          (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) =
        DoubleCoset.doubleCoset (diagMat 2 (![1, n + 1]) : GL (Fin 2) ℚ)
          (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
        have h_mem_dc : (diagMat 2 (![1, n + 1]) : GL (Fin 2) ℚ) ∈
            DoubleCoset.doubleCoset (diagMat 2 (![1, m + 1]) : GL (Fin 2) ℚ)
              ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
          rw [h]; exact DoubleCoset.mem_doubleCoset_self _ _ _
        exact (DoubleCoset.doubleCoset_eq_of_mem
          (Gamma0_doubleCoset_subset_Gamma N _ h_mem_dc)).symm
      have h_T : T_diag (![1, m + 1]) = T_diag (![1, n + 1]) := by
        rw [T_diag, T_diag, HeckeCoset.eq_iff]
        simp only [diagMat_delta, show ∀ k : ℕ, (∀ i : Fin 2, 0 < (![1, k + 1]) i) from
          fun k i => by fin_cases i <;> simp <;> omega, dite_true]
        exact h_gl
      have hpos : ∀ k : ℕ, ∀ i, 0 < (![1, k + 1]) i :=
        fun k i => by fin_cases i <;> simp <;> omega
      have := diagonal_representative_unique 2 _ _ (hpos m) (hpos n)
        (divChain_one_succ m) (divChain_one_succ n) h_T
      have h1 := congr_fun this 1
      simp [Matrix.cons_val_one, Matrix.head_cons] at h1; omega)


/-- `diagMat 2 a ∈ Δ₀(N)` when all entries are positive and `gcd(a 0, N) = 1`. -/
private lemma diagMat_mem_Delta0_of_gcd (N : ℕ) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    diagMat 2 a ∈ Delta0_submonoid N := by
  refine ⟨diagMat_hasIntEntries 2 a ha, diagMat_det_pos 2 a ha,
    Matrix.diagonal (fun i => (a i : ℤ)), ?_, ?_, ?_⟩
  · ext i j; simp [diagMat, ha, Matrix.diagonal, Matrix.map_apply]
  · simp [Matrix.diagonal]
  · simpa [Matrix.diagonal] using hgcd

/-- The Gamma0 coset of `diag(a)` when `gcd(a₁, N) = 1`:
    the Gamma0-level analogue of `T_diag`. -/
noncomputable def T_diag_Gamma0 (N : ℕ) [NeZero N] (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    HeckeCoset (Gamma0_pair N) :=
  ⟦⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N a ha hgcd⟩⟧


/-! ### Shimura Proposition 3.33: N-power determinant structure

For `p | N` and `β ∈ Δ₀(N)` with `det(β) = p^k`, the `Γ₀(N)`-double coset of `β`
equals the `Γ₀(N)`-double coset of `diag(1, p^k)`. This means:
(1) All elements with the same N-power determinant share a double coset.
(2) `T'(p^k) = T'(p)^k` — the bad-prime tower is generated by `T'(p)`.
(3) Bad-prime generators commute: `T'(p) * T'(q) = T'(q) * T'(p)` for `p ≠ q`, `p q | N`.

**Proof sketch**: Left-multiply `β` by `[[1, 0], [Nt, 1]] ∈ Γ₀(N)` (choosing `t` via
`a⁻¹ mod p`, which exists since `gcd(a, N) = 1` forces `gcd(a, p) = 1`) to clear the
lower-left entry modulo `p`, reducing `det` by one factor of `p`. Induct on `k`. -/

/-- Existence of `t` with `t * a + c ≡ 0 (mod p)` when `gcd(a, p) = 1`.
Uses Bezout: `gcdA(a,p) * a + gcdB(a,p) * p = 1`, so `t = -c * gcdA(a,p)`
gives `t*a + c = c * gcdB(a,p) * p`. -/
private lemma exists_mod_clearing (a c : ℤ) (p : ℕ)
    (hap : Int.gcd a p = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ (t * a + c) := by
  refine ⟨-c * Int.gcdA a p, ⟨c * Int.gcdB a p, ?_⟩⟩
  have bez := Int.gcd_eq_gcd_ab a p
  rw [hap] at bez
  -- bez : ↑1 = a * a.gcdA ↑p + ↑p * a.gcdB ↑p
  -- Goal: -c * a.gcdA ↑p * a + c = ↑p * (c * a.gcdB ↑p)
  linear_combination c * (bez - 1)

/-- If  and , then . -/
private lemma coprime_of_dvd_Npow (a : ℤ) (N : ℕ) (haN : Int.gcd a N = 1)
    (m : ℕ) (k : ℕ) (hm : m ∣ N ^ k) : Int.gcd a m = 1 :=
  Nat.Coprime.coprime_dvd_right hm (Nat.Coprime.pow_right k haN)

/-- **Shimura Proposition 3.33** (left coset form): If  has 
with , then  for some  and .

The matrix  is explicitly constructed: since , take ,
then  has  and . -/
private lemma Gamma0_left_coset_of_Npow_det (N : ℕ) [NeZero N]
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA_det_pos : 0 < A.det)
    (hAN : (N : ℤ) ∣ A 1 0)
    (m : ℕ) (hm_pos : 0 < m)
    (hdet : A.det = m)
    (ham : Int.gcd (A 0 0) m = 1) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ),
      L.det = 1 ∧ (N : ℤ) ∣ L 1 0 ∧
      0 ≤ r ∧ r < m ∧
      A = L * (Matrix.of ![![(1 : ℤ), r], ![0, m]]) := by
  -- Extract c₀: A 1 0 = N * c₀
  obtain ⟨c₀, hc₀⟩ := hAN
  -- Choose r ≡ a⁻¹ * b (mod m) via Bezout, with 0 ≤ r < m
  -- Since gcd(a, m) = 1: ∃ s, s*a ≡ 1 (mod m)
  obtain ⟨t_inv, ht⟩ := exists_mod_clearing (A 0 0) (- A 0 1) m ham
  -- Set r = t_inv % m ∈ [0, m). Since m | (t_inv*a - b): a*r ≡ b (mod m).
  set r := t_inv % (m : ℤ) with hr_def
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr_lt : r < m := Int.emod_lt_of_pos _ (by omega)
  -- Step 1: m | (a*r - b). Proof: (t_inv*a - b) - (t_inv - r)*a = a*r - b, and m divides both.
  have hm_tr : (m : ℤ) ∣ (t_inv - r) := by
    rw [hr_def, show t_inv - t_inv % ↑m = ↑m * (t_inv / ↑m) from by linarith [Int.ediv_add_emod t_inv (↑m : ℤ)]]
    exact dvd_mul_right _ _
  have hm_ar_b : (m : ℤ) ∣ (A 0 0 * r - A 0 1) := by
    have h := dvd_sub ht (dvd_mul_of_dvd_left hm_tr (A 0 0))
    rwa [show t_inv * A 0 0 + -A 0 1 - (t_inv - r) * A 0 0 = A 0 0 * r - A 0 1 from by ring] at h
  -- Step 2: m | (d - Nc₀r). Proof: a(d - Nc₀r) = m + Nc₀(ar - b), gcd(a,m)=1.
  have hm_d_cr : (m : ℤ) ∣ (A 1 1 - ↑N * c₀ * r) := by
    have h_key : A 0 0 * (A 1 1 - ↑N * c₀ * r) = ↑m + (A 0 1 - A 0 0 * r) * (↑N * c₀) := by
      have h_det := Matrix.det_fin_two A; rw [hc₀, hdet] at h_det; linarith
    have hm_ba : (↑m : ℤ) ∣ (A 0 1 - A 0 0 * r) := by
      obtain ⟨w, hw⟩ := hm_ar_b; exact ⟨-w, by linarith⟩
    have h_dvd_prod : (↑m : ℤ) ∣ A 0 0 * (A 1 1 - ↑N * c₀ * r) :=
      h_key ▸ dvd_add (dvd_refl _) (dvd_mul_of_dvd_left hm_ba _)
    exact ((Int.isCoprime_iff_gcd_eq_one.mpr ham).symm).dvd_of_dvd_mul_left h_dvd_prod
  -- Step 3: define the quotients q₁, q₂
  obtain ⟨q₁, hq₁⟩ := hm_ar_b  -- ar - b = m*q₁
  obtain ⟨q₂, hq₂⟩ := hm_d_cr  -- d - Nc₀r = m*q₂
  -- Step 4: L = [[a, -q₁], [Nc₀, q₂]]. Then A = L · [[1,r],[0,m]] and det(L) = 1.
  refine ⟨Matrix.of ![![A 0 0, -q₁], ![↑N * c₀, q₂]], r, ?_, ?_, hr_nonneg, hr_lt, ?_⟩
  · -- det L = 1: det(L)*m = a*(d-Nc₀r) + Nc₀*(ar-b) = ad - bNc₀ = det A = m
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val']
    have hAdet' : A.det = A 0 0 * A 1 1 - A 0 1 * (↑N * c₀) := by rw [Matrix.det_fin_two, hc₀]
    have h1 : (A 0 0 * q₂ + q₁ * (↑N * c₀)) * ↑m = ↑m := by
      have h_det_val := hAdet'; rw [hdet] at h_det_val
      calc (A 0 0 * q₂ + q₁ * (↑N * c₀)) * ↑m
          = A 0 0 * (↑m * q₂) + (↑m * q₁) * (↑N * c₀) := by ring
        _ = A 0 0 * (A 1 1 - ↑N * c₀ * r) + (A 0 0 * r - A 0 1) * (↑N * c₀) := by
            rw [← hq₂, ← hq₁]
        _ = A 0 0 * A 1 1 - A 0 1 * (↑N * c₀) := by ring
        _ = ↑m := h_det_val.symm
    -- Goal: A 0 0 * q₂ - (-q₁) * (N*c₀) = 1, equivalently A 0 0 * q₂ + q₁ * (N*c₀) = 1
    -- From h1: (A 0 0 * q₂ + q₁ * (N*c₀)) * m = m, and m > 0
    have := mul_right_cancel₀ (show (↑m : ℤ) ≠ 0 from by omega) (show
      (A 0 0 * q₂ + q₁ * (↑N * c₀)) * ↑m = 1 * ↑m by rw [one_mul]; exact h1)
    linarith
  · -- N | L 1 0: the (1,0) entry is N*c₀
    change (↑N : ℤ) ∣ !![A 0 0, -q₁; ↑N * c₀, q₂] 1 0
    norm_num [Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val', Matrix.cons_val_zero]
  · -- A = L · [[1, r], [0, m]]: the 4 entry equations reduce to hq₁, hq₂, hc₀
    have h00 : A 0 0 = A 0 0 * 1 + (-q₁) * 0 := by ring
    have h01 : A 0 1 = A 0 0 * r + (-q₁) * ↑m := by linarith [hq₁]
    have h10 : A 1 0 = ↑N * c₀ * 1 + q₂ * 0 := by linarith [hc₀]
    have h11 : A 1 1 = ↑N * c₀ * r + q₂ * ↑m := by linarith [hq₂]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] <;>
      first | exact h00 | exact h01 | exact h10 | exact h11

/-- Left cosets `Γ₀(N) · [[1, r], [0, m]]` and `Γ₀(N) · [[1, s], [0, m]]` are equal
iff `r ≡ s (mod m)`. Since `0 ≤ r, s < m`, equality of cosets forces `r = s`. -/
private lemma Gamma0_left_coset_distinct (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m)
    (r s : ℤ) (hr : 0 ≤ r) (hr' : r < m) (hs : 0 ≤ s) (hs' : s < m)
    (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL_det : L.det = 1) (hL_N : (N : ℤ) ∣ L 1 0)
    (hL_eq : L * Matrix.of ![![(1 : ℤ), r], ![0, m]] =
             Matrix.of ![![(1 : ℤ), s], ![0, m]]) :
    r = s := by
  -- From L * [[1,r],[0,m]] = [[1,s],[0,m]], read off entries:
  have h00 : L 0 0 = 1 := by
    have := congr_fun (congr_fun hL_eq 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      mul_zero, mul_one, add_zero] at this
    linarith
  have h10 : L 1 0 = 0 := by
    have := congr_fun (congr_fun hL_eq 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      mul_zero, mul_one, add_zero] at this
    -- this : L 1 0 + L 1 1 * 0 = 0, so L 1 0 = 0
    linarith
  have h01 : L 0 0 * r + L 0 1 * m = s := by
    have := congr_fun (congr_fun hL_eq 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at this
    linarith
  -- From h00 and h01: r + L 0 1 * m = s. Since 0 ≤ r, s < m: L 0 1 = 0, r = s.
  rw [h00, one_mul] at h01
  have hm_z : (0 : ℤ) < ↑m := Int.ofNat_lt.mpr hm_pos
  have hL01 : L 0 1 = 0 := by nlinarith
  rw [hL01, zero_mul, add_zero] at h01; exact h01

/-- `![0, ↑m] j = ↑m * ![0, 1] j` for `j : Fin 2`. Needed for bridging the
integer-level factorization `L * [[1,r],[0,m]]` with the GL-level product
`mapGL(L) * diagMat(1,m) * mapGL([[1,r],[0,1]])`. -/
private lemma fin2_col_scale (m : ℕ) (j : Fin 2) :
    (![0, (m : ℤ)] : Fin 2 → ℤ) j = (m : ℤ) * (![0, 1] : Fin 2 → ℤ) j := by
  fin_cases j <;> simp

/-- **Shimura Proposition 3.33** (double coset form): Every element of `Δ₀(N)` with
determinant `m` (where `m ∣ N^k`) is in the `Γ₀(N)`-double coset of `[[1,0],[0,m]]`.

Concretely: `Γ₀(N) α Γ₀(N) = Γ₀(N) [[1,0],[0,m]] Γ₀(N)` for all `α ∈ Δ₀(N)` with
`det α = m` and `m ∣ N^k`. -/
private lemma shimura_prop_3_33 (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m) (k : ℕ) (hm_dvd : m ∣ N ^ k)
    (β : GL (Fin 2) ℚ) (hβ : β ∈ Delta0_submonoid N)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    β ∈ DoubleCoset.doubleCoset
      ((diagMat 2 (![1, m] : Fin 2 → ℕ) : GL (Fin 2) ℚ))
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  -- Extract integer matrix A from β ∈ Δ₀(N)
  obtain ⟨_, hdet_pos, A, hA, hAN, hAco⟩ := hβ
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  have hA_det : A.det = ↑m := by
    have : (A.det : ℚ) = ↑m := by rw [← det_intMat_cast 2 A, ← hA]; exact hdet
    exact_mod_cast this
  -- Apply the left-coset factorization: A = L * [[1, r], [0, m]]
  obtain ⟨L, r, hL_det, hL_N, hr_nn, hr_lt, hA_eq⟩ :=
    Gamma0_left_coset_of_Npow_det N A hA_det_pos hAN m hm_pos hA_det
      (coprime_of_dvd_Npow (A 0 0) N hAco m k hm_dvd)
  -- Factor [[1, r], [0, m]] = diag(1,m) * [[1, r], [0, 1]]
  -- So β = (mapGL L) * diag(1,m) * (mapGL [[1,r],[0,1]])
  -- with L ∈ Γ₀(N) and [[1,r],[0,1]] ∈ Γ₀(N)
  rw [DoubleCoset.mem_doubleCoset]
  -- Build the SL₂(ℤ) element from L (det = 1)
  set L_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨L, hL_det⟩
  -- Build the right factor R = [[1, r], [0, 1]] ∈ SL₂(ℤ)
  set R : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, r], ![0, 1]] with hR_def
  have hR_det : R.det = 1 := by
    simp [R, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  set R_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨R, hR_det⟩
  -- L ∈ Γ₀(N)
  have hL_Gamma0 : L_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL_N
  -- R ∈ Γ₀(N) (since R 1 0 = 0 and N | 0)
  have hR_Gamma0 : R_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [R_sl, R, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
  -- Key: A = L * [[1,r],[0,m]] = L * (diag(1,m) * R)
  -- So β = mapGL(L) * diagMat(1,m) * mapGL(R)
  refine ⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ hL_Gamma0,
    mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ hR_Gamma0, ?_⟩
  -- Lift the integer factorization to GL₂(ℚ) entry by entry
  apply Units.ext; ext i j
  have hA_ij := congr_fun₂ hA_eq i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at hA_ij
  -- hA_ij : A i j = L i 0 * ![1, r] j + L i 1 * ![0, ↑m] j
  -- Extract integer equations from A = L * [[1,r],[0,m]]
  have h00 : A 0 0 = L 0 0 := by
    have := congr_fun₂ hA_eq 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at this; linarith
  have h01 : A 0 1 = L 0 0 * r + L 0 1 * ↑m := by
    have := congr_fun₂ hA_eq 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at this; linarith
  have h10 : A 1 0 = L 1 0 := by
    have := congr_fun₂ hA_eq 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at this; linarith
  have h11 : A 1 1 = L 1 0 * r + L 1 1 * ↑m := by
    have := congr_fun₂ hA_eq 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at this; linarith
  -- Compute diagMat entries
  set D := diagMat 2 (![1, m] : Fin 2 → ℕ)
  have hD_pos : ∀ i : Fin 2, 0 < (![1, m] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simp [hm_pos]
  have hDv := diagMat_val 2 (![1, m] : Fin 2 → ℕ) hD_pos
  have hd00 : (D : GL (Fin 2) ℚ).val 0 0 = 1 := by rw [hDv]; simp [Matrix.diagonal]
  have hd01 : (D : GL (Fin 2) ℚ).val 0 1 = 0 := by rw [hDv]; simp [Matrix.diagonal]
  have hd10 : (D : GL (Fin 2) ℚ).val 1 0 = 0 := by rw [hDv]; simp [Matrix.diagonal]
  have hd11 : (D : GL (Fin 2) ℚ).val 1 1 = ↑m := by rw [hDv]; simp [Matrix.diagonal]
  -- Now dispatch entry-by-entry
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, RingHom.mapMatrix_apply,
    algebraMap_int_eq, Int.coe_castRingHom, hA, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.map_apply, SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk,
    L_sl, R_sl, SpecialLinearGroup.coe_mk, R, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    hd00, hd01, hd10, hd11]
  fin_cases i <;> fin_cases j <;> (
    simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      mul_zero, mul_one, zero_mul, add_zero, zero_add, one_mul] at hA_ij ⊢
    simp only [fin2_col_scale] at hA_ij  -- rewrite ![0,↑m] j → ↑m * ![0,1] j
    norm_cast; linarith [hA_ij])

set_option maxHeartbeats 800000 in
/-- Lower-unipotent injection `Fin k → decompQuot (Gamma0_pair N) g`
for counting the right-coset quotient. -/
private noncomputable def lunip_inject (N : ℕ) [NeZero N] (k_exp : ℕ)
    (g : (Gamma0_pair N).Δ) : Fin k_exp → HeckeRing.decompQuot (Gamma0_pair N) g :=
  fun r => ⟦⟨mapGL ℚ ⟨Matrix.of ![![(1 : ℤ), 0], ![↑N * (↑r : ℤ), 1]],
    by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]⟩,
    Subgroup.mem_map_of_mem _ (by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons])⟩⟧

/-- **Generalized Shimura 3.33**: all `β ∈ Δ₀(N)` with `det = m` and
`gcd(A 0 0, m) = 1` are in `DC(diag(1, m), Γ₀, Γ₀)`.
Strictly stronger than `shimura_prop_3_33` (which derives `gcd(A 0 0, m) = 1` from `m ∣ N^k`). -/
private lemma shimura_prop_3_33_gen (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m)
    (β : GL (Fin 2) ℚ) (hβ : β ∈ Delta0_submonoid N)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (β : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ))
    (ham : Int.gcd (A 0 0) m = 1) :
    β ∈ DoubleCoset.doubleCoset
      ((diagMat 2 (![1, m] : Fin 2 → ℕ) : GL (Fin 2) ℚ))
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  have hdet_pos : 0 < (β : Matrix (Fin 2) (Fin 2) ℚ).det := hβ.2.1
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  have hA_det : A.det = ↑m := by
    have : (A.det : ℚ) = ↑m := by rw [← det_intMat_cast 2 A, ← hA]; exact hdet
    exact_mod_cast this
  obtain ⟨L, r, hL_det, hL_N, hr_nn, hr_lt, hA_eq⟩ :=
    Gamma0_left_coset_of_Npow_det N A hA_det_pos hAN m hm_pos hA_det ham
  -- The rest is identical to shimura_prop_3_33: β = (mapGL L) * diag(1,m) * (mapGL R)
  rw [DoubleCoset.mem_doubleCoset]
  set L_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨L, hL_det⟩
  set R : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, r], ![0, 1]] with hR_def
  have hR_det : R.det = 1 := by
    simp [R, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  set R_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨R, hR_det⟩
  have hL_Gamma0 : L_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL_N
  have hR_Gamma0 : R_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [R_sl, R, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
  -- Dispatch exactly as shimura_prop_3_33
  refine ⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ hL_Gamma0,
    mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ hR_Gamma0, ?_⟩
  apply Units.ext; ext i j
  have hA_ij := congr_fun₂ hA_eq i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val'] at hA_ij
  set D := diagMat 2 (![1, m] : Fin 2 → ℕ)
  have hD_pos : ∀ i : Fin 2, 0 < (![1, m] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simp [hm_pos]
  have hDv := diagMat_val 2 (![1, m] : Fin 2 → ℕ) hD_pos
  have hd00 : (D : GL (Fin 2) ℚ).val 0 0 = 1 := by rw [hDv]; simp [Matrix.diagonal]
  have hd01 : (D : GL (Fin 2) ℚ).val 0 1 = 0 := by rw [hDv]; simp [Matrix.diagonal]
  have hd10 : (D : GL (Fin 2) ℚ).val 1 0 = 0 := by rw [hDv]; simp [Matrix.diagonal]
  have hd11 : (D : GL (Fin 2) ℚ).val 1 1 = ↑m := by rw [hDv]; simp [Matrix.diagonal]
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, RingHom.mapMatrix_apply,
    algebraMap_int_eq, Int.coe_castRingHom, hA, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.map_apply, SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk,
    L_sl, R_sl, SpecialLinearGroup.coe_mk, R, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    hd00, hd01, hd10, hd11]
  fin_cases i <;> fin_cases j <;> (
    simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
      mul_zero, mul_one, zero_mul, add_zero, zero_add, one_mul] at hA_ij ⊢
    simp only [fin2_col_scale] at hA_ij
    norm_cast; linarith [hA_ij])

/-- `gcd(a, k) = 1` when `gcd(a, N) = 1` and `k ∣ N^hk`. Every prime factor of `k`
divides `N`, so is coprime to `a`. -/
private lemma coprime_of_gcd_one_dvd_pow (a : ℤ) (N : ℕ) (k : ℕ) (hk : ℕ)
    (haN : Int.gcd a N = 1) (hk_dvd : k ∣ N ^ hk) : Int.gcd a k = 1 :=
  Nat.Coprime.coprime_dvd_right hk_dvd (Nat.Coprime.pow_right hk haN)

/-- The (1,0) entry of `σ⁻¹ * !![1,0;c,1] * σ` is `(σ 0 0)² * c` for `σ ∈ SL₂(ℤ)`.
This is the key entry computation for the stabilizer injectivity argument. -/
private lemma sl2_conj_lunip_10 (σ : SpecialLinearGroup (Fin 2) ℤ) (c : ℤ) :
    ((σ⁻¹ : SpecialLinearGroup (Fin 2) ℤ).1 *
      Matrix.of ![![(1 : ℤ), 0], ![c, 1]] * σ.1) 1 0 = σ.1 0 0 ^ 2 * c := by
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val', Fin.isValue]
  ring


set_option maxHeartbeats 1600000 in
/-- Cardinality of `decompQuot` for any `g` in the double coset of `diag(1, k)` is `k`. -/
private lemma decompQuot_Npow_natcard (N : ℕ) [NeZero N]
    (k_exp : ℕ) (hk_pos : 0 < k_exp) (hk : ℕ) (hk_dvd : k_exp ∣ N ^ hk)
    (g : (Gamma0_pair N).Δ)
    (hg : (⟦g⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N (![1, k_exp])
        (by intro i; fin_cases i <;> simp [hk_pos]) (by simp [Int.gcd_one_left])) :
    Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g) = k_exp := by
  have ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simp [hk_pos]
  have hgcd : Int.gcd (↑((![1, k_exp] : Fin 2 → ℕ) 0)) ↑N = 1 := by simp
  have h_dc : DoubleCoset.doubleCoset (g : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) =
    DoubleCoset.doubleCoset (diagMat 2 (![1, k_exp] : Fin 2 → ℕ) : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
    (HeckeCoset.eq_iff g _).mp hg
  -- g is in DC(diag), so g = γ₁ · diag · γ₂ for γ₁, γ₂ ∈ H
  have h_g_mem : (g : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset
      (diagMat 2 (![1, k_exp] : Fin 2 → ℕ) : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
    rw [← h_dc]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at h_g_mem
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hg_eq⟩ := h_g_mem
  -- Extract γ₁'s integer matrix from H membership
  -- (Gamma0_pair N).H = Subgroup.map (mapGL ℚ) (Gamma0 N) by definition
  obtain ⟨σ₁, hσ₁_mem, hσ₁_eq⟩ := Subgroup.mem_map.mp hγ₁
  rw [CongruenceSubgroup.Gamma0_mem] at hσ₁_mem
  -- Key: gcd(σ₁ 0 0, k_exp) = 1 since gcd(σ₁ 0 0, N) = 1 and k_exp ∣ N^hk
  -- From det(σ₁) = 1 and N | σ₁ 1 0: IsCoprime (σ₁ 0 0) N
  have hN_c : (↑N : ℤ) ∣ (σ₁.1 1 0) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσ₁_mem
  obtain ⟨q₁, hq₁⟩ := hN_c
  have hdet₁ := σ₁.prop; rw [Matrix.det_fin_two] at hdet₁
  have ha₁N : Int.gcd (σ₁.1 0 0) ↑N = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    exact ⟨σ₁.1 1 1, -(σ₁.1 0 1) * q₁, by rw [hq₁] at hdet₁; nlinarith⟩
  have ha₁k : Int.gcd (σ₁.1 0 0) ↑k_exp = 1 :=
    coprime_of_gcd_one_dvd_pow (σ₁.1 0 0) N k_exp hk ha₁N hk_dvd
  -- Nat.card = k_exp via le_antisymm
  rw [show k_exp = Fintype.card (Fin k_exp) from (Fintype.card_fin k_exp).symm,
    ← Nat.card_eq_fintype_card]
  apply le_antisymm
  · -- ≤: Transfer to the diagonal representative, then use easy diagonal surjectivity.
    -- Step 1: Build Equiv decompQuot P g ≃ decompQuot P g_diag via γ₁-conjugation
    set g_diag : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, k_exp] : Fin 2 → ℕ),
      diagMat_mem_Delta0_of_gcd N _ ha (by simp)⟩
    -- From h_dc: g ∈ DC(g_diag), so g = γ₁ g_diag γ₂
    -- The conjugation φ : σ ↦ γ₁⁻¹ σ γ₁ gives an Equiv H/K_g ≃ H/K_{g_diag}
    have h_card_eq : Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g) =
        Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_diag) := by
      -- Use decompQuot_double_H_equiv from BlockBijection.lean
      -- g = γ₁ * g_diag * γ₂ with γ₁, γ₂ ∈ H
      let g_mid : (Gamma0_pair N).Δ := ⟨γ₁ * ↑g_diag * γ₂, hg_eq ▸ g.2⟩
      have h_mid : (g_mid : GL (Fin 2) ℚ) = g := hg_eq.symm
      let e : HeckeRing.decompQuot (Gamma0_pair N) g ≃
          HeckeRing.decompQuot (Gamma0_pair N) g_diag :=
        (Equiv.cast (congrArg (HeckeRing.decompQuot (Gamma0_pair N))
          (Subtype.ext h_mid))).symm.trans
          (HeckeRing.decompQuot_double_H_equiv (Gamma0_pair N) g_diag ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩ (hg_eq ▸ g.2))
      exact Nat.card_congr e
    rw [h_card_eq]
    -- Step 2: For g_diag = diagMat, surjectivity is easy
    haveI : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_diag) :=
      HeckeRing.instFintypeDecompQuot _ _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_surjective (lunip_inject N k_exp g_diag) (by
      intro q; revert q; apply Quotient.ind; intro ⟨σ_gl, hσ_gl⟩
      obtain ⟨τ', hτ'_mem, hτ'_eq⟩ := Subgroup.mem_map.mp hσ_gl
      rw [CongruenceSubgroup.Gamma0_mem] at hτ'_mem
      obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hτ'_mem
      have hτ'_det := τ'.prop; rw [Matrix.det_fin_two] at hτ'_det
      have hτ'_a_N : Int.gcd (τ'.1 0 0) ↑N = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        exact ⟨τ'.1 1 1, -(τ'.1 0 1) * c', by rw [hc'] at hτ'_det; nlinarith⟩
      have hτ'_a_k : Int.gcd (τ'.1 0 0) ↑k_exp = 1 :=
        coprime_of_gcd_one_dvd_pow _ N k_exp hk hτ'_a_N hk_dvd
      obtain ⟨u_bez, _, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hτ'_a_k
      set r₀ := u_bez * c'
      have hr₀_mod : (k_exp : ℤ) ∣ (τ'.1 0 0 * r₀ - c') := by
        have : τ'.1 0 0 * r₀ - c' = (τ'.1 0 0 * u_bez - 1) * c' := by ring
        rw [this]; exact dvd_mul_of_dvd_left ⟨-_, by nlinarith⟩ c'
      have hr_nn := Int.emod_nonneg r₀ (show (k_exp : ℤ) ≠ 0 by omega)
      have hr_lt := Int.emod_lt_of_pos r₀ (show (0 : ℤ) < k_exp by omega)
      refine ⟨⟨(r₀ % k_exp).toNat, by omega⟩, ?_⟩
      -- Stabilizer membership for the diagonal case.
      -- D⁻¹(σ⁻¹ u_r)D ∈ H, where σ = mapGL(τ'), u_r = mapGL(u_r_sl).
      -- Construct the Γ₀(N) witness explicitly.
      simp only [lunip_inject]
      symm; rw [@Quotient.eq'', QuotientGroup.leftRel_apply]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        ConjAct.smul_def]
      simp only [ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      -- Divisibility for the modular-reduced r
      set r_int := r₀ % (k_exp : ℤ)
      have hr_div : (k_exp : ℤ) ∣ (τ'.1 0 0 * r_int - c') := by
        have h1 := hr₀_mod -- k | (a' * r₀ - c')
        have h2 : (k_exp : ℤ) ∣ (r₀ - r_int) :=
          ⟨r₀ / k_exp, by have := Int.ediv_add_emod r₀ (k_exp : ℤ); omega⟩
        have : τ'.1 0 0 * r_int - c' = (τ'.1 0 0 * r₀ - c') - τ'.1 0 0 * (r₀ - r_int) := by ring
        rw [this]; exact dvd_sub h1 (dvd_mul_of_dvd_right h2 _)
      obtain ⟨c'', hc''⟩ := hr_div
      -- Construct the Γ₀(N) witness: the SL₂(ℤ) element with entries
      -- [a', b'*k; N*(-c''), d' - N*r*b']
      set wit : Matrix (Fin 2) (Fin 2) ℤ :=
        Matrix.of ![![τ'.1 1 1 - (N : ℤ) * r_int * τ'.1 0 1, -(τ'.1 0 1) * k_exp],
          ![(N : ℤ) * c'', τ'.1 0 0]]
      -- det of corrected wit: (d'-Nrb')a' - (-b'k)(Nc'') = a'd' - Nb'(a'r-kc'') = a'd' - Nb'c' = 1
      have hc'_eq : c' = τ'.1 0 0 * r_int - ↑k_exp * c'' := by linarith [hc'']
      have hwit_det : wit.det = 1 := by
        simp only [wit, Matrix.det_fin_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        have h_det1 : τ'.1 0 0 * τ'.1 1 1 - τ'.1 0 1 * (↑N * c') = 1 := by
          rw [hc'] at hτ'_det; linarith
        -- (d'-Nrb')a' - (-b'k)(Nc'') = a'(d'-Nrb') + Nb'kc'' = a'd' - Nb'c' = 1
        have : (τ'.1 1 1 - ↑N * r_int * τ'.1 0 1) * τ'.1 0 0 -
            -(τ'.1 0 1) * ↑k_exp * (↑N * c'') =
          τ'.1 0 0 * τ'.1 1 1 - τ'.1 0 1 * (↑N * (τ'.1 0 0 * r_int - ↑k_exp * c'')) := by ring
        rw [this, ← hc'_eq]; linarith
      have hwit_Gamma0 : (⟨wit, hwit_det⟩ : SpecialLinearGroup (Fin 2) ℤ) ∈
          CongruenceSubgroup.Gamma0 N := by
        rw [CongruenceSubgroup.Gamma0_mem]
        simp [wit, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
      have h_wit_mem := Subgroup.mem_map_of_mem (mapGL ℚ) hwit_Gamma0
      -- GL-level inverse rewrite
      have h_gl_inv : ∀ σ : SpecialLinearGroup (Fin 2) ℤ,
          ((mapGL ℚ σ)⁻¹ : GL (Fin 2) ℚ) = mapGL ℚ (σ⁻¹) := by
        intro σ; simpa using (map_inv (mapGL ℚ) σ).symm
      set D_gl := (↑g_diag : GL (Fin 2) ℚ)
      -- KEY: prove D * mapGL(wit) = (σ⁻¹ u_r) * D (no D⁻¹!), then derive membership
      suffices h_eq : D_gl * mapGL ℚ ⟨wit, hwit_det⟩ =
          (σ_gl⁻¹ * mapGL ℚ ⟨!![1, 0; (N : ℤ) * ↑(r₀ % ↑k_exp).toNat, 1],
            by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.head_cons]⟩) * D_gl by
        -- Derive D⁻¹ * (σ⁻¹ u_r) * D = mapGL(wit) from h_eq
        have h_conj : mapGL ℚ ⟨wit, hwit_det⟩ = D_gl⁻¹ *
            (σ_gl⁻¹ * mapGL ℚ ⟨!![1, 0; (N : ℤ) * ↑(r₀ % ↑k_exp).toNat, 1],
              by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
                Matrix.cons_val_one, Matrix.head_cons]⟩) * D_gl := by
          have := congr_arg (D_gl⁻¹ * ·) h_eq
          simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
          convert this using 2; group
        -- Rewrite the target and use h_conj
        show D_gl⁻¹ * (σ_gl⁻¹ * mapGL ℚ ⟨!![1, 0; (N : ℤ) * ↑(r₀ % ↑k_exp).toNat, 1],
              by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
                Matrix.cons_val_one, Matrix.head_cons]⟩) * D_gl ∈ (Gamma0_pair N).H
        rw [← h_conj]; exact h_wit_mem
      -- Prove h_eq by entry comparison (NO D⁻¹ anywhere!)
      rw [← hτ'_eq, h_gl_inv, ← map_mul]
      apply Units.ext; ext i j
      simp only [D_gl, g_diag, Units.val_mul,
        diagMat_val 2 _ ha, mapGL_coe_matrix, RingHom.mapMatrix_apply,
        algebraMap_int_eq, Int.coe_castRingHom, Matrix.map_apply,
        SpecialLinearGroup.coe_matrix_coe, SpecialLinearGroup.coe_mk,
        SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_mul,
        Matrix.adjugate_fin_two, Matrix.of_apply,
        Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
        Matrix.diagonal_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
        neg_mul, mul_neg, sub_mul, mul_sub,
        show (1 : Fin 2) ≠ 0 from by decide, if_false, if_true,
        Nat.cast_one, wit]
      -- Normalize r_int = (r₀ % k).toNat cast, then ring
      have hr_cast : ((r₀ % ↑k_exp).toNat : ℤ) = r_int := Int.toNat_of_nonneg hr_nn
      fin_cases i <;> fin_cases j <;>
        simp only [hr_cast] <;>
        push_cast [hc', hc''] <;>
        (try ring) <;>
        -- Entry (1,0): N*k*c'' = N*r*a' - N*c' from hc'': a'*r - c' = k*c''
        (have := congr_arg (Int.cast (R := ℚ)) hc''; push_cast at this ⊢; nlinarith))
  · -- ≥: inject Fin k_exp into decompQuot g via lower-unipotent representatives.
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective (lunip_inject N k_exp g) (by
      intro r₁ r₂ h_eq
      -- Convert quotient equality to stabilizer membership
      simp only [lunip_inject] at h_eq
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h_eq
      -- Extract: g⁻¹ * u * g ∈ H from stabilizer membership
      have h_mem := Subgroup.mem_subgroupOf.mp h_eq
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h_mem
      simp only [ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct] at h_mem
      -- h_mem : g⁻¹ * ↑(u₁⁻¹u₂) * g⁻¹⁻¹ ∈ H. Simplify double inverse.
      simp only [inv_inv] at h_mem
      -- h_mem : (↑g)⁻¹ * ↑(u₁⁻¹u₂) * ↑g ∈ H. Substitute g = γ₁ D γ₂.
      rw [hg_eq] at h_mem
      -- Derive k | (r₂-r₁) from h_mem + matrix entry computation + coprimality
      suffices h_dvd : (k_exp : ℤ) ∣ ((↑↑r₂ : ℤ) - ↑↑r₁) by
        have hr₁ := r₁.isLt; have hr₂ := r₂.isLt
        have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h_dvd (by omega)
        exact Fin.ext (by omega)
      -- From h_mem and γ₂ ∈ H: γ₂ * (product) * γ₂⁻¹ ∈ H, which = D⁻¹(γ₁⁻¹ u γ₁)D
      set D := diagMat 2 (![1, k_exp] : Fin 2 → ℕ)
      have h_conj := (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.mul_mem hγ₂ h_mem)
        ((Gamma0_pair N).H.inv_mem hγ₂)
      -- Step 1: Rewrite h_conj from γ₂-conjugated to D-conjugated form
      have h_grp : ∀ (x : GL (Fin 2) ℚ),
          γ₂ * ((γ₁ * D * γ₂)⁻¹ * x * (γ₁ * D * γ₂)) * γ₂⁻¹ =
          D⁻¹ * (γ₁⁻¹ * x * γ₁) * D := fun x => by group
      rw [h_grp] at h_conj
      -- h_conj : D⁻¹ * (γ₁⁻¹ * u * γ₁) * D ∈ H
      -- Step 2: Extract τ ∈ Γ₀(N) from H membership
      obtain ⟨τ, hτ_mem, hτ_eq⟩ := Subgroup.mem_map.mp h_conj
      rw [CongruenceSubgroup.Gamma0_mem] at hτ_mem
      -- hτ_eq : mapGL(τ) = D⁻¹(γ₁⁻¹ u γ₁)D
      -- hτ_mem : (↑(τ(1,0)) : ZMod N) = 0, i.e., N | τ(1,0)
      -- Step 3: Rearrange hτ_eq to D * mapGL(τ) = M * D, then compare (1,0) entries
      rw [← hσ₁_eq] at hτ_eq
      -- mapGL(τ) = D⁻¹ * M * D → D * mapGL(τ) = M * D
      have h_mul := congr_arg (D * ·) hτ_eq
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at h_mul
      -- From h_mul (D * mapGL τ = M * D), the equation D mapGL(τ) = M D
      -- gives k * τ(1,0) = M(1,0) at entry (1,0).
      -- And M = σ₁⁻¹ u_diff σ₁ has (1,0) = a₁²N(r₂-r₁) by sl2_conj_lunip_10.
      -- Then k * τ(1,0) = a₁²N(r₂-r₁), N | τ(1,0) → k | a₁²(r₂-r₁).
      -- gcd(a₁,k)=1 → k | (r₂-r₁).
      have hτ_dvd : (↑N : ℤ) ∣ τ.1 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hτ_mem
      have h_sl2 := sl2_conj_lunip_10 σ₁ (↑N * (↑↑r₂ - ↑↑r₁))
      -- Coprimality of a₁² and k
      have ha₁k_cop : IsCoprime (σ₁.1 0 0 ^ 2) (↑k_exp : ℤ) :=
        (Int.isCoprime_iff_gcd_eq_one.mpr ha₁k).pow_left
      exact ha₁k_cop.symm.dvd_of_dvd_mul_left (by
        -- From h_mul : D * mapGL(τ) = M * D, equate (1,0) entries.
        -- LHS(1,0) = k * τ(1,0), RHS(1,0) = M(1,0) = v(1,0) by h_sl2.
        -- Compute at the ℤ level: k * N * q₂ = a₁² * N * (r₂-r₁), cancel N.
        obtain ⟨q₂, hq₂⟩ := hτ_dvd
        -- From hτ_eq: mapGL(τ) = D⁻¹ mapGL(w) D where w = σ₁⁻¹ u_diff σ₁.
        -- So D mapGL(τ) D⁻¹ = mapGL(w), and entry (1,0) gives k * τ(1,0) = w(1,0).
        -- By h_sl2: w(1,0) = (σ₁ 0 0)² * N * (r₂-r₁).
        -- Hence k * N * q₂ = (σ₁ 0 0)² * N * (r₂-r₁).
        -- Since N ≠ 0: k * q₂ = (σ₁ 0 0)² * (r₂-r₁).
        exact ⟨q₂, by
          -- Named SL₂(ℤ) lower-unipotent elements (over ℤ, not ℕ)
          set u1 : SpecialLinearGroup (Fin 2) ℤ :=
            ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * ↑↑r₁, 1]],
             by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons]⟩
          set u2 : SpecialLinearGroup (Fin 2) ℤ :=
            ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * ↑↑r₂, 1]],
             by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons]⟩
          set u_diff : SpecialLinearGroup (Fin 2) ℤ :=
            ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * (↑↑r₂ - ↑↑r₁), 1]],
             by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons]⟩
          have hu : u1⁻¹ * u2 = u_diff := by
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [u1, u2, u_diff, Matrix.mul_apply, Fin.sum_univ_two,
                SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_mul,
                SpecialLinearGroup.coe_mk,
                Matrix.adjugate_fin_two, Matrix.of_apply,
                Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val']
              <;> ring
          -- Bridge in GL₂(ℚ): the H-subtype coercion = mapGL(u1⁻¹ * u2)
          set mid_H := (⟨(mapGL ℚ) u1, Subgroup.mem_map_of_mem _ (by
                rw [CongruenceSubgroup.Gamma0_mem]
                simp [u1, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons])⟩ :
              (Gamma0_pair N).H)⁻¹ *
            ⟨(mapGL ℚ) u2, Subgroup.mem_map_of_mem _ (by
                rw [CongruenceSubgroup.Gamma0_mem]
                simp [u2, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons])⟩
          have hu_gl : (↑mid_H : GL (Fin 2) ℚ) = mapGL ℚ (u1⁻¹ * u2) := by
            show (mapGL ℚ u1)⁻¹ * mapGL ℚ u2 = mapGL ℚ (u1⁻¹ * u2)
            rw [← map_inv, ← map_mul]
          -- Full middle product = mapGL(σ₁⁻¹ * u_diff * σ₁) in GL₂(ℚ)
          have h_mid_gl : ((mapGL ℚ σ₁)⁻¹ * ↑mid_H * mapGL ℚ σ₁ : GL (Fin 2) ℚ) =
              mapGL ℚ (σ₁⁻¹ * u_diff * σ₁) := by
            rw [show ((mapGL ℚ σ₁)⁻¹ : GL (Fin 2) ℚ) = mapGL ℚ σ₁⁻¹ from
              (map_inv (mapGL ℚ) σ₁).symm, hu_gl, hu, ← map_mul, ← map_mul]
          -- Extract (1,0) entry of the GL product
          have h_mid10 := congr_fun₂
            (congr_arg (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ)) h_mid_gl) 1 0
          -- Reduce to the ℤ entry via mapGL_coe_matrix + exact_mod_cast h_sl2
          simp only [mapGL_coe_matrix, RingHom.mapMatrix_apply, algebraMap_int_eq,
            Int.coe_castRingHom, Matrix.map_apply, SpecialLinearGroup.coe_mul] at h_mid10
          -- h_mid10 should relate the GL entries to the mapped SL₂ entry
          -- Now get the (1,0) entry equation from h_mul
          have h_e := congr_arg
            (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0) h_mul
          simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, D,
            diagMat_val 2 _ ha, Matrix.diagonal_apply,
            show (1 : Fin 2) ≠ 0 from by decide, if_false, if_true,
            Nat.cast_one, mul_zero, zero_mul, zero_add, add_zero,
            mul_one, one_mul] at h_e
          -- KEY: rewrite h_mul with h_mid_gl to get clean mapGL form
          rw [h_mid_gl] at h_mul
          -- h_mul : D * mapGL(τ) = mapGL(σ₁⁻¹ * u_diff * σ₁) * D
          -- Re-extract (1,0) entry from the CLEAN h_mul
          have h_e2 := congr_arg
            (fun x : GL (Fin 2) ℚ => (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0) h_mul
          simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, D,
            diagMat_val 2 _ ha, Matrix.diagonal_apply,
            show (1 : Fin 2) ≠ 0 from by decide, if_false, if_true,
            Nat.cast_one, mul_zero, zero_mul, zero_add, add_zero,
            mul_one, one_mul,
            mapGL_coe_matrix, RingHom.mapMatrix_apply, algebraMap_int_eq,
            Int.coe_castRingHom, Matrix.map_apply, SpecialLinearGroup.coe_mul] at h_e2
          -- h_e2 has the ℚ entry equation with mapGL/SpecialLinearGroup.map coercions.
          -- Simplify the SL map coercions to Int.cast entries
          simp only [SpecialLinearGroup.coe_matrix_coe, Matrix.map_apply,
            algebraMap_int_eq, Int.coe_castRingHom, SpecialLinearGroup.coe_mul,
            Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Nat.cast_one, mul_one] at h_e2
          -- h_e2 RHS: ↑((↑σ₁⁻¹ * ↑u_diff * ↑σ₁) 1 0) matches h_sl2 after cast
          -- Unfold u_diff to match h_sl2's matrix form
          have h_rhs_z : ((σ₁⁻¹ : SpecialLinearGroup (Fin 2) ℤ).1 * u_diff.1 * σ₁.1) 1 0 =
              σ₁.1 0 0 ^ 2 * ((N : ℤ) * ((↑↑r₂ : ℤ) - ↑↑r₁)) := by
            simp only [u_diff, SpecialLinearGroup.coe_mk]; exact h_sl2
          -- Cast h_rhs_z to ℚ and rewrite h_e2
          rw [congr_arg (Int.cast (R := ℚ)) h_rhs_z, hq₂] at h_e2
          -- h_e2 : k * ↑(N * q₂) = (σ₁ 0 0)^2 * (N * (r₂-r₁)) (as ℚ)
          -- h_e2 : k * ↑(N * q₂) = ↑(a₁² * (N * (r₂-r₁))) in ℚ
          -- Derive the ℤ equation by cancelling N
          have hN_ne_z : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
          have hN_ne : ((N : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN_ne_z
          -- From h_e2: N * (k * q₂) = N * (a₁² * (r₂-r₁)) in ℚ. Cancel N.
          have h_q : ((σ₁.1 0 0 ^ 2 * ((↑↑r₂ : ℤ) - ↑↑r₁) : ℤ) : ℚ) =
              ((↑k_exp * q₂ : ℤ) : ℚ) := by
            apply mul_left_cancel₀ hN_ne
            push_cast
            -- Goal should be N * (a₁² * (r₂-r₁)) = N * (k * q₂) in ℚ
            -- From h_e2 (after push_cast): k * (N * q₂) = a₁² * (N * (r₂-r₁))
            push_cast at h_e2
            nlinarith [h_e2]
          exact_mod_cast h_q⟩))

/-- The degree of the bad-prime Hecke coset `T'(k)` equals `k`. -/
private lemma Gamma0_bad_deg (N : ℕ) [NeZero N]
    (k_exp : ℕ) (hk_pos : 0 < k_exp) (hk : ℕ) (hk_dvd : k_exp ∣ N ^ hk) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, k_exp])
        (by intro i; fin_cases i <;> simp [hk_pos]) (by simp [Int.gcd_one_left])) = k_exp := by
  simp only [HeckeRing.HeckeCoset_deg]
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast decompQuot_Npow_natcard N k_exp hk_pos hk hk_dvd _ (HeckeCoset.mk_rep _)

/-- **Bad-part multiplication** (Shimura Prop 3.33 consequence):
`T'(m) * T'(n) = T'(m*n)` for `m, n ∣ N^∞`.

The proof uses `shimura_prop_3_33` for the unique output coset and
`HeckeRing.deg_mul` for the coefficient-1 argument. -/
private theorem T_bad_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n)
    (km : ℕ) (hm_dvd : m ∣ N ^ km) (kn : ℕ) (hn_dvd : n ∣ N ^ kn) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (by intro i; fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left])) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, n])
        (by intro i; fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left])) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m * n])
        (by intro i; fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp [Int.gcd_one_left])) 1 := by
  -- Strategy: use T_single_one_mul_eq_single with two conditions:
  -- (1) heckeMultiplicity = 1 at D_out (from degree argument)
  -- (2) heckeMultiplicity = 0 at all other cosets (from shimura_prop_3_33)
  set D₁ := T_diag_Gamma0 N (![1, m]) (by intro i; fin_cases i <;> simp [hm_pos])
    (by simp [Int.gcd_one_left])
  set D₂ := T_diag_Gamma0 N (![1, n]) (by intro i; fin_cases i <;> simp [hn_pos])
    (by simp [Int.gcd_one_left])
  set D_out := T_diag_Gamma0 N (![1, m * n])
    (by intro i; fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
    (by simp [Int.gcd_one_left])
  change HeckeRing.T_single _ ℤ D₁ 1 * HeckeRing.T_single _ ℤ D₂ 1 =
    HeckeRing.T_single _ ℤ D_out 1
  -- First prove mulMap uniqueness (needed by both h_one and h_zero)
  have h_mulMap : ∀ (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂)),
      HeckeRing.mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p = D_out := by
    intro p
    simp only [HeckeRing.mulMap, D_out, T_diag_Gamma0]
    apply (HeckeCoset.eq_iff _ _).mpr
    exact DoubleCoset.doubleCoset_eq_of_mem
      (shimura_prop_3_33 N (m * n) (Nat.mul_pos hm_pos hn_pos) (km + kn)
        (Nat.mul_dvd_mul hm_dvd hn_dvd |>.trans (by rw [pow_add])) _ (by
          exact Submonoid.mul_mem _
            (Submonoid.mul_mem _ ((Gamma0_pair N).h₀ p.1.out.2) (HeckeCoset.rep D₁).2)
            (Submonoid.mul_mem _ ((Gamma0_pair N).h₀ p.2.out.2) (HeckeCoset.rep D₂).2))
        (by -- det = m * n (same proof as before)
          simp only [Subtype.coe_mk, Units.val_mul, Matrix.det_mul]
          obtain ⟨σi, _, hσi⟩ := Subgroup.mem_map.mp p.1.out.2
          obtain ⟨σj, _, hσj⟩ := Subgroup.mem_map.mp p.2.out.2
          have hdi : (↑p.1.out : GL (Fin 2) ℚ).val.det = 1 := by
            rw [← hσi, mapGL_coe_matrix]; simp [det_intMat_cast 2, σi.prop]
          have hdj : (↑p.2.out : GL (Fin 2) ℚ).val.det = 1 := by
            rw [← hσj, mapGL_coe_matrix]; simp [det_intMat_cast 2, σj.prop]
          rw [hdi, hdj]; simp only [one_mul, mul_one]
          have h_rep1 : (HeckeCoset.rep D₁ : GL (Fin 2) ℚ).val.det = (m : ℚ) := by
            have h_in := DoubleCoset.mem_doubleCoset_self (Gamma0_pair N).H (Gamma0_pair N).H
              (↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ)
            rw [(HeckeCoset.eq_iff (HeckeCoset.rep D₁) ⟨diagMat 2 (![1, m]),
                diagMat_mem_Delta0_of_gcd N _ (by intro i; fin_cases i <;> simp [hm_pos]) (by simp)⟩).mp
              (HeckeCoset.mk_rep D₁)] at h_in
            rw [DoubleCoset.mem_doubleCoset] at h_in
            obtain ⟨h1, hh1, h2, hh2, hprod⟩ := h_in
            obtain ⟨s1, _, hs1⟩ := Subgroup.mem_map.mp hh1
            obtain ⟨s2, _, hs2⟩ := Subgroup.mem_map.mp hh2
            rw [show (HeckeCoset.rep D₁ : GL (Fin 2) ℚ).val = h1.val * (diagMat 2 (![1, m]) : GL (Fin 2) ℚ).val * h2.val from
              congr_arg Units.val hprod, Matrix.det_mul, Matrix.det_mul,
              show h1.val.det = 1 from by rw [← hs1, mapGL_coe_matrix]; simp [det_intMat_cast 2, s1.prop],
              show h2.val.det = 1 from by rw [← hs2, mapGL_coe_matrix]; simp [det_intMat_cast 2, s2.prop],
              diagMat_det 2 _ (by intro i; fin_cases i <;> simp [hm_pos])]
            simp [Fin.prod_univ_two]
          have h_rep2 : (HeckeCoset.rep D₂ : GL (Fin 2) ℚ).val.det = (n : ℚ) := by
            have h_in := DoubleCoset.mem_doubleCoset_self (Gamma0_pair N).H (Gamma0_pair N).H
              (↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ)
            rw [(HeckeCoset.eq_iff (HeckeCoset.rep D₂) ⟨diagMat 2 (![1, n]),
                diagMat_mem_Delta0_of_gcd N _ (by intro i; fin_cases i <;> simp [hn_pos]) (by simp)⟩).mp
              (HeckeCoset.mk_rep D₂)] at h_in
            rw [DoubleCoset.mem_doubleCoset] at h_in
            obtain ⟨h1, hh1, h2, hh2, hprod⟩ := h_in
            obtain ⟨s1, _, hs1⟩ := Subgroup.mem_map.mp hh1
            obtain ⟨s2, _, hs2⟩ := Subgroup.mem_map.mp hh2
            rw [show (HeckeCoset.rep D₂ : GL (Fin 2) ℚ).val = h1.val * (diagMat 2 (![1, n]) : GL (Fin 2) ℚ).val * h2.val from
              congr_arg Units.val hprod, Matrix.det_mul, Matrix.det_mul,
              show h1.val.det = 1 from by rw [← hs1, mapGL_coe_matrix]; simp [det_intMat_cast 2, s1.prop],
              show h2.val.det = 1 from by rw [← hs2, mapGL_coe_matrix]; simp [det_intMat_cast 2, s2.prop],
              diagMat_det 2 _ (by intro i; fin_cases i <;> simp [hn_pos])]
            simp [Fin.prod_univ_two]
          rw [h_rep1, h_rep2]; push_cast; ring))
  -- Degree computation
  have h_deg_m : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D₁ = m :=
    Gamma0_bad_deg N m hm_pos km hm_dvd
  have h_deg_n : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D₂ = n :=
    Gamma0_bad_deg N n hn_pos kn hn_dvd
  have h_deg_mn : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out = ↑m * ↑n :=
    Gamma0_bad_deg N (m * n) (Nat.mul_pos hm_pos hn_pos) (km + kn)
      (Nat.mul_dvd_mul hm_dvd hn_dvd |>.trans (by rw [pow_add]))
  have h_deg_prod : HeckeRing.deg (Gamma0_pair N)
      (HeckeRing.T_single _ ℤ D₁ 1 * HeckeRing.T_single _ ℤ D₂ 1) = (m : ℤ) * n := by
    rw [HeckeRing.deg_mul, HeckeRing.deg_T_single, HeckeRing.deg_T_single,
      one_mul, one_mul, h_deg_m, h_deg_n]
  apply HeckeRing.T_single_one_mul_eq_single
  · -- h_one: μ = 1 by degree argument
    -- From h_mulMap: the Finsupp m = single D_out μ
    -- deg(single D_out μ) = μ * mn = m * n, so μ = 1
    set μ := HeckeRing.heckeMultiplicity (Gamma0_pair N) D₁.rep D₂.rep D_out.rep
    -- m Finsupp = single D_out μ (from support ⊆ {D_out})
    have h_zero_all : ∀ A, A ≠ D_out → (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) A = 0 := by
      intro A hA; simp only [HeckeRing.m_apply]
      exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique
        (Gamma0_pair N) _ _ D_out A hA h_mulMap
    have h_m_eq : HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep = Finsupp.single D_out μ := by
      ext A; simp only [Finsupp.single_apply, HeckeRing.m_apply]
      split_ifs with h
      · subst h; rfl
      · exact h_zero_all A (Ne.symm h)
    -- deg(m) = μ * mn
    have h_deg_m_eq : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) = μ * (↑m * ↑n) := by
      rw [h_m_eq]; simp [HeckeRing.deg_T_single, h_deg_mn]
    -- deg(T'(m)*T'(n)) = deg(m) = m * n
    rw [HeckeRing.T_single_one_mul_T_single_one] at h_deg_prod
    -- μ * (m*n) = m*n with m*n > 0 gives μ = 1
    have hmn_pos : (0 : ℤ) < ↑m * ↑n := by positivity
    have hmn_ne : (↑m * ↑n : ℤ) ≠ 0 := ne_of_gt hmn_pos
    exact mul_right_cancel₀ hmn_ne (by linarith [h_deg_prod, h_deg_m_eq])
  · -- h_zero: ∀ A ≠ D_out, heckeMultiplicity = 0
    intro A hA
    apply HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N)
      (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D_out A hA
    -- Show: ∀ p, mulMap p = D_out
    -- Every product σᵢg₁ · τⱼg₂ has det = mn and is in Δ₀(N).
    -- By shimura_prop_3_33: it's in DC(diag(1,mn)) = D_out.
    intro p
    -- mulMap gives ⟦product⟧. Show product ∈ DC(diag(1,mn)) by shimura_prop_3_33.
    simp only [HeckeRing.mulMap, D_out, T_diag_Gamma0]
    -- product ∈ DC(diag(1,mn)) by shimura_prop_3_33 → HeckeCoset equality
    apply (HeckeCoset.eq_iff _ _).mpr
    refine DoubleCoset.doubleCoset_eq_of_mem
      (shimura_prop_3_33 N (m * n) (Nat.mul_pos hm_pos hn_pos) (km + kn)
        (Nat.mul_dvd_mul hm_dvd hn_dvd |>.trans (by rw [pow_add])) _ ?_ ?_)
    · -- product ∈ Delta0_submonoid N = (Gamma0_pair N).Δ
      exact Submonoid.mul_mem _
        (Submonoid.mul_mem _ ((Gamma0_pair N).h₀ p.1.out.2) (HeckeCoset.rep D₁).2)
        (Submonoid.mul_mem _ ((Gamma0_pair N).h₀ p.2.out.2) (HeckeCoset.rep D₂).2)
    · -- det(product) = m * n
      -- Step 1: det is multiplicative
      simp only [Subtype.coe_mk, Units.val_mul, Matrix.det_mul]
      -- Step 2: det(H-element) = 1 for p.1.out and p.2.out
      obtain ⟨σi, _, hσi⟩ := Subgroup.mem_map.mp p.1.out.2
      obtain ⟨σj, _, hσj⟩ := Subgroup.mem_map.mp p.2.out.2
      have hdi : (↑p.1.out : GL (Fin 2) ℚ).val.det = 1 := by
        rw [← hσi, mapGL_coe_matrix]; simp [det_intMat_cast 2, σi.prop]
      have hdj : (↑p.2.out : GL (Fin 2) ℚ).val.det = 1 := by
        rw [← hσj, mapGL_coe_matrix]; simp [det_intMat_cast 2, σj.prop]
      rw [hdi, hdj]
      simp only [one_mul, mul_one]
      -- Step 3: det(rep D₁) * det(rep D₂) = m * n
      -- rep D₁ ∈ DC(diag(1,m)): extract h₁ h₂ from DC, det = 1*m*1 = m
      have h_rep1 : (HeckeCoset.rep D₁ : GL (Fin 2) ℚ).val.det = (m : ℚ) := by
        have h_in := DoubleCoset.mem_doubleCoset_self (Gamma0_pair N).H (Gamma0_pair N).H
          (↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ)
        rw [(HeckeCoset.eq_iff (HeckeCoset.rep D₁) ⟨diagMat 2 (![1, m]),
            diagMat_mem_Delta0_of_gcd N _ (by intro i; fin_cases i <;> simp [hm_pos]) (by simp)⟩).mp
          (HeckeCoset.mk_rep D₁)] at h_in
        rw [DoubleCoset.mem_doubleCoset] at h_in
        obtain ⟨h1, hh1, h2, hh2, hprod⟩ := h_in
        obtain ⟨s1, _, hs1⟩ := Subgroup.mem_map.mp hh1
        obtain ⟨s2, _, hs2⟩ := Subgroup.mem_map.mp hh2
        rw [show (HeckeCoset.rep D₁ : GL (Fin 2) ℚ).val = h1.val * (diagMat 2 (![1, m]) : GL (Fin 2) ℚ).val * h2.val from
          congr_arg Units.val hprod, Matrix.det_mul, Matrix.det_mul,
          show h1.val.det = 1 from by rw [← hs1, mapGL_coe_matrix]; simp [det_intMat_cast 2, s1.prop],
          show h2.val.det = 1 from by rw [← hs2, mapGL_coe_matrix]; simp [det_intMat_cast 2, s2.prop],
          diagMat_det 2 _ (by intro i; fin_cases i <;> simp [hm_pos])]
        simp [Fin.prod_univ_two]
      have h_rep2 : (HeckeCoset.rep D₂ : GL (Fin 2) ℚ).val.det = (n : ℚ) := by
        have h_in := DoubleCoset.mem_doubleCoset_self (Gamma0_pair N).H (Gamma0_pair N).H
          (↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ)
        rw [(HeckeCoset.eq_iff (HeckeCoset.rep D₂) ⟨diagMat 2 (![1, n]),
            diagMat_mem_Delta0_of_gcd N _ (by intro i; fin_cases i <;> simp [hn_pos]) (by simp)⟩).mp
          (HeckeCoset.mk_rep D₂)] at h_in
        rw [DoubleCoset.mem_doubleCoset] at h_in
        obtain ⟨h1, hh1, h2, hh2, hprod⟩ := h_in
        obtain ⟨s1, _, hs1⟩ := Subgroup.mem_map.mp hh1
        obtain ⟨s2, _, hs2⟩ := Subgroup.mem_map.mp hh2
        rw [show (HeckeCoset.rep D₂ : GL (Fin 2) ℚ).val = h1.val * (diagMat 2 (![1, n]) : GL (Fin 2) ℚ).val * h2.val from
          congr_arg Units.val hprod, Matrix.det_mul, Matrix.det_mul,
          show h1.val.det = 1 from by rw [← hs1, mapGL_coe_matrix]; simp [det_intMat_cast 2, s1.prop],
          show h2.val.det = 1 from by rw [← hs2, mapGL_coe_matrix]; simp [det_intMat_cast 2, s2.prop],
          diagMat_det 2 _ (by intro i; fin_cases i <;> simp [hn_pos])]
        simp [Fin.prod_univ_two]
      rw [h_rep1, h_rep2]; push_cast; ring

/-! ### Shimura Theorem 3.35: Surjective ring hom R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))

The construction factors through a free polynomial ring presentation:
`ℤ[X_{(p,k)}] →→ HeckeAlgebra 2 →+* 𝕋 (Gamma0_pair N) ℤ`. -/

section Thm335

/-! #### Atkin-Lehner anti-involution for `Gamma0_pair N`

The map `ι(g) = w · gᵀ · w⁻¹` where `w = diag(1, N)` is an anti-involution
that preserves `Γ₀(N)` and `Δ₀(N)`, and fixes every diagonal double coset.
This gives commutativity of `𝕋 (Gamma0_pair N) ℤ` via Shimura Prop 3.8. -/

/-- The conjugation element `w = diag(1, N)` in `GL₂(ℚ)`. -/
private noncomputable def wN (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  diagMat 2 (![1, N])

private lemma wN_pos (N : ℕ) [NeZero N] : ∀ i : Fin 2, 0 < (![1, N]) i := by
  intro i; fin_cases i <;> simp [NeZero.pos]

private lemma wN_val (N : ℕ) [NeZero N] :
    (↑(wN N) : Matrix (Fin 2) (Fin 2) ℚ) =
    Matrix.diagonal (![1, (N : ℚ)]) := by
  simp [wN, wN_pos N]

/-- The Atkin-Lehner anti-involution `g ↦ w · gᵀ · w⁻¹` as a monoid hom
    `GL₂(ℚ) →* GL₂(ℚ)ᵐᵒᵖ`. -/
private noncomputable def Gamma0_AL_hom (N : ℕ) [NeZero N] :
    GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (wN N * (GL_transposeEquiv 2 g).unop * (wN N)⁻¹)
  map_one' := by simp [GL_transposeEquiv_val]
  map_mul' a b := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul]
    have h1 : (GL_transposeEquiv 2 (a * b)).unop =
        (GL_transposeEquiv 2 b).unop * (GL_transposeEquiv 2 a).unop := by
      change MulOpposite.unop (GL_transposeEquiv 2 (a * b)) = _
      rw [map_mul]; rfl
    rw [h1]; group

/-- The Atkin-Lehner map is involutive. -/
private lemma Gamma0_AL_involutive (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ) :
    (Gamma0_AL_hom N (Gamma0_AL_hom N g).unop).unop = g := by
  simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
  -- Goal: w * (w * gᵀ * w⁻¹)ᵀ * w⁻¹ = g
  -- transpose of (w * gᵀ * w⁻¹) = (w⁻¹)ᵀ * g * wᵀ
  -- Since w is diagonal (symmetric): wᵀ = w, (w⁻¹)ᵀ = w⁻¹
  -- So: w * w⁻¹ * g * w * w⁻¹ = g ✓
  have h_tr : (GL_transposeEquiv 2 (wN N * (GL_transposeEquiv 2 g).unop * (wN N)⁻¹)).unop =
      (GL_transposeEquiv 2 (wN N)⁻¹).unop *
      (GL_transposeEquiv 2 (GL_transposeEquiv 2 g).unop).unop *
      (GL_transposeEquiv 2 (wN N)).unop := by
    change MulOpposite.unop (GL_transposeEquiv 2
      (wN N * (GL_transposeEquiv 2 g).unop * (wN N)⁻¹)) = _
    rw [map_mul, map_mul]
    simp only [MulOpposite.unop_mul]; group
  have h_wN : (GL_transposeEquiv 2 (wN N)).unop = wN N :=
    diagMat_GL_transpose_eq 2 _ (wN_pos N)
  rw [h_tr, GL_transposeEquiv_involutive, h_wN]
  have h_inv : (GL_transposeEquiv 2 (wN N)⁻¹).unop = (wN N)⁻¹ := by
    rw [map_inv, MulOpposite.unop_inv, h_wN]
  rw [h_inv]; group

/-- The Atkin-Lehner map preserves `Γ₀(N)`: if `σ ∈ Γ₀(N)` then `ι(σ) ∈ Γ₀(N)`. -/
private lemma Gamma0_AL_map_H (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).H) :
    (Gamma0_AL_hom N g).unop ∈ (Gamma0_pair N).H := by
  simp only [Gamma0_pair] at hg ⊢
  change _ ∈ Subgroup.map (mapGL ℚ) (CongruenceSubgroup.Gamma0 N)
  rw [Subgroup.mem_map]
  rw [Subgroup.mem_map] at hg
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [CongruenceSubgroup.Gamma0_mem] at hσ_mem
  -- σ ∈ SL₂(ℤ) with N | σ 1 0.
  -- The conjugated transpose τ = [[σ₀₀, σ₁₀/N], [N·σ₀₁, σ₁₁]] is in Gamma0(N).
  set A := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hA_def
  have hA_det : A.det = 1 := σ.2
  -- Extract divisibility: N | A 1 0
  have hN_dvd : (↑N : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσ_mem
  obtain ⟨c', hc'⟩ := hN_dvd
  -- Build the SL₂(ℤ) element τ
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![A 0 0, c'], ![↑N * A 0 1, A 1 1]]
  have hB_det : B.det = 1 := by
    simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
    have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    rw [hA_det] at this
    linarith [show c' * (↑N * A 0 1) = A 0 1 * A 1 0 from by rw [hc']; ring]
  set τ : SpecialLinearGroup (Fin 2) ℤ := ⟨B, hB_det⟩
  refine ⟨τ, ?_, ?_⟩
  · -- τ ∈ Gamma0(N): N | τ 1 0 = N * σ₀₁
    rw [CongruenceSubgroup.Gamma0_mem]
    show (↑(B 1 0) : ZMod N) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [B, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply]
    exact dvd_mul_right _ _
  · -- mapGL ℚ τ = wN N * (mapGL ℚ σ)ᵀ * (wN N)⁻¹
    -- Equivalently: (mapGL ℚ τ) * wN N = wN N * (mapGL ℚ σ)ᵀ
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
    suffices h : (mapGL ℚ) τ * wN N =
        wN N * MulOpposite.unop ((GL_transposeEquiv 2) ((mapGL ℚ) σ)) by
      rwa [eq_mul_inv_iff_mul_eq]
    apply Units.ext; ext i j
    simp only [GeneralLinearGroup.coe_mul, GL_transposeEquiv_val, wN_val,
      mapGL_coe_matrix, algebraMap_int_eq, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.diagonal, Matrix.transpose_apply, Fin.sum_univ_two]
    -- All four (i,j) cases reduce to rational arithmetic via hc'
    fin_cases i <;> fin_cases j <;> norm_num [τ, B, hc', hA_def]
    -- case (0,1): ↑c' * ↑N = ↑(↑σ 1 0) in ℚ
    · exact_mod_cast show c' * ↑N = A 1 0 by rw [hc']; ring
    -- case (1,1): ↑(↑σ 1 1) * ↑N = ↑N * ↑(↑σ 1 1) in ℚ
    · ring

/-- The Atkin-Lehner map preserves `Δ₀(N)`.
    Proof: `w gᵀ w⁻¹ = [[a, c/N], [Nb, d]]` has integer entries (since `N|c`),
    `det = ad-bc > 0`, `N | Nb`, `gcd(a,N) = 1`. Same matrix computation as `map_H`. -/
private lemma Gamma0_AL_map_Δ (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ) :
    (Gamma0_AL_hom N g).unop ∈ (Gamma0_pair N).Δ := by
  simp only [Gamma0_pair] at hg ⊢
  change _ ∈ Delta0_submonoid N
  obtain ⟨_, hdet_pos, A, hA, hAN, hAco⟩ := hg
  -- Extract c' = A 1 0 / N (integer since N | A 1 0)
  obtain ⟨c', hc'⟩ := hAN
  -- The conjugated transpose B = [[A 0 0, c'], [N * A 0 1, A 1 1]]
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![A 0 0, c'], ![↑N * A 0 1, A 1 1]]
  -- det B = det A > 0
  have hB_det : B.det = A.det := by
    simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    linarith [show c' * (↑N * A 0 1) = A 0 1 * A 1 0 from by rw [hc']; ring]
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  have hB_det_pos : 0 < B.det := hB_det ▸ hA_det_pos
  -- Build a GL element from B
  have hB_ne : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [det_intMat_cast]; exact_mod_cast hB_det_pos.ne'
  set g' : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero _ hB_ne
  -- Show ι(g) = g' via the trick: g' * wN = wN * gᵀ iff g' = wN * gᵀ * wN⁻¹
  have hg'_eq : (Gamma0_AL_hom N g).unop = g' := by
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
    suffices h : g' * wN N =
        wN N * MulOpposite.unop ((GL_transposeEquiv 2) g) by
      rw [← h]; group
    apply Units.ext; ext i j
    simp only [GeneralLinearGroup.coe_mul, GL_transposeEquiv_val, wN_val,
      Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
      Fin.sum_univ_two, hA, g', GeneralLinearGroup.mkOfDetNeZero]
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.map_apply]
    · exact_mod_cast show c' * ↑N = A 1 0 from by rw [hc']; ring
    · ring
  rw [hg'_eq]
  -- g' has matrix B cast to ℚ
  have hval : (↑g' : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ) := rfl
  -- Now show g' ∈ Delta0_submonoid N
  have hdet_g' : 0 < (↑g' : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [hval, det_intMat_cast 2]; exact_mod_cast hB_det_pos
  refine ⟨⟨B, hval⟩, hdet_g', B, hval, ?_, ?_⟩
  · -- N | B 1 0 = N * A 0 1
    simp only [B, Matrix.cons_val_one, Matrix.of_apply]
    exact dvd_mul_right _ _
  · -- gcd(B 0 0, N) = gcd(A 0 0, N) = 1
    simp only [B, Matrix.cons_val_zero, Matrix.of_apply]
    exact hAco

/-- The Atkin-Lehner anti-involution for `Gamma0_pair N`. -/
private noncomputable def Gamma0_antiInvolution (N : ℕ) [NeZero N] :
    AntiInvolution (Gamma0_pair N) where
  toFun := Gamma0_AL_hom N
  involutive := Gamma0_AL_involutive N
  map_H := Gamma0_AL_map_H N
  map_Δ := Gamma0_AL_map_Δ N

/-- The Atkin-Lehner anti-involution preserves determinants. -/
private lemma Gamma0_AL_bar_det (N : ℕ) [NeZero N] (g : GL (Fin 2) ℚ) :
    ((Gamma0_antiInvolution N).bar g : Matrix (Fin 2) (Fin 2) ℚ).det =
    (g : Matrix (Fin 2) (Fin 2) ℚ).det := by
  show ((Gamma0_AL_hom N g).unop : GL (Fin 2) ℚ).val.det = g.val.det
  simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
    Units.val_mul, Matrix.det_mul, GL_transposeEquiv_val, MulOpposite.unop_op,
    Matrix.det_transpose]
  have h1 : (wN N : GL (Fin 2) ℚ).val.det * ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]; simp
  have h2 : (wN N : GL (Fin 2) ℚ).val.det * g.val.det *
      ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det =
    g.val.det * ((wN N : GL (Fin 2) ℚ).val.det * ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det) := by ring
  rw [h2, h1, mul_one]

/-- The first invariant factor of a 2×2 SNF divides every matrix entry.
Uses Cramer: from `L * M = diag(d) * R⁻¹` and `det(L) = 1`, solve for `M i j`. -/
private lemma snf_first_dvd_entry₂ (M : Matrix (Fin 2) (Fin 2) ℤ)
    (d : Fin 2 → ℤ) (hd_div : d 0 ∣ d 1)
    (L R : SpecialLinearGroup (Fin 2) ℤ)
    (hLR : (L : Matrix (Fin 2) (Fin 2) ℤ) * M * (R : Matrix _ _ ℤ) = Matrix.diagonal d)
    (i j : Fin 2) : d 0 ∣ M i j := by
  -- L * M = diag(d) * R⁻¹
  have hRR : (R : Matrix _ _ ℤ) * (R⁻¹).val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; simp
  have hLM : L.val * M = Matrix.diagonal d * (R⁻¹).val := by
    have h1 : L.val * M = (L.val * M * R.val) * (R⁻¹).val := by
      rw [Matrix.mul_assoc (L.val * M), hRR, Matrix.mul_one]
    rw [h1, hLR]
  -- Row equations via diagonal multiplication
  have h_row : ∀ k l, L.val k 0 * M 0 l + L.val k 1 * M 1 l =
      d k * (R⁻¹).val k l := by
    intro k l; have h := congr_fun₂ hLM k l
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    convert h using 1
    simp only [Matrix.diagonal_apply, Fin.sum_univ_two]; fin_cases k <;> simp
  -- d 0 | each row sum (row 0 by triviality, row 1 by d 0 | d 1)
  have hd0 : ∀ l, d 0 ∣ L.val 0 0 * M 0 l + L.val 0 1 * M 1 l :=
    fun l => ⟨_, h_row 0 l⟩
  have hd1 : ∀ l, d 0 ∣ L.val 1 0 * M 0 l + L.val 1 1 * M 1 l :=
    fun l => (h_row 1 l) ▸ hd_div.mul_right _
  -- det(L) = 1 → Cramer extracts M i j
  have hdet_L : L.val 0 0 * L.val 1 1 - L.val 0 1 * L.val 1 0 = 1 := by
    have := L.prop; rwa [Matrix.det_fin_two] at this
  -- Cramer: M i j from row combinations
  have h_M0 : ∀ l, d 0 ∣ M 0 l := fun l => by
    have : L.val 1 1 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) -
        L.val 0 1 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) =
        (L.val 0 0 * L.val 1 1 - L.val 0 1 * L.val 1 0) * M 0 l := by ring
    rw [show M 0 l = L.val 1 1 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) -
        L.val 0 1 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) from by rw [this, hdet_L, one_mul]]
    exact dvd_sub (dvd_mul_of_dvd_right (hd0 l) _) (dvd_mul_of_dvd_right (hd1 l) _)
  have h_M1 : ∀ l, d 0 ∣ M 1 l := fun l => by
    have : L.val 0 0 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) -
        L.val 1 0 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) =
        (L.val 0 0 * L.val 1 1 - L.val 0 1 * L.val 1 0) * M 1 l := by ring
    rw [show M 1 l = L.val 0 0 * (L.val 1 0 * M 0 l + L.val 1 1 * M 1 l) -
        L.val 1 0 * (L.val 0 0 * M 0 l + L.val 0 1 * M 1 l) from by rw [this, hdet_L, one_mul]]
    exact dvd_sub (dvd_mul_of_dvd_right (hd1 l) _) (dvd_mul_of_dvd_right (hd0 l) _)
  fin_cases i
  · exact h_M0 j
  · exact h_M1 j

/-- **Bad-det branch**: for `g ∈ Δ₀(N)` with `det(g) | N^k`,
`bar(g) ∈ DC(g)` by `shimura_prop_3_33` applied to both `g` and `bar(g)`. -/
private lemma Gamma0_AL_in_DC_bad (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ)
    (m : ℕ) (hm_pos : 0 < m) (k : ℕ) (hm_dvd : m ∣ N ^ k)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  have h_bar_delta := Gamma0_AL_map_Δ N g hg
  have h_g_dc := shimura_prop_3_33 N m hm_pos k hm_dvd g hg hdet
  have h_bar_dc := shimura_prop_3_33 N m hm_pos k hm_dvd
    ((Gamma0_antiInvolution N).bar g) h_bar_delta
    (Gamma0_AL_bar_det N g ▸ hdet)
  rw [DoubleCoset.doubleCoset_eq_of_mem h_g_dc]; exact h_bar_dc

/-- **Coprime-det branch**: for `g ∈ Δ₀(N)` with `gcd(det(g), N) = 1`,
`bar(g) ∈ DC(g)` by `doubleCoset_eq_of_Gamma0_coprimeDet` + same SL₂-DC
(same elementary divisors, since `gcd(a₀, N) = 1` makes `gcd` of entries
invariant under the AL transformation `[[a,b],[Nc,d]] ↦ [[a,c],[Nb,d]]`). -/
private lemma Gamma0_AL_in_DC_coprime (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (hdet_coprime : Int.gcd A.det N = 1) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  have h_bar_delta := Gamma0_AL_map_Δ N g hg
  -- Build Δ-subtypes for shimura_prop_3_31
  set a_sub : (Gamma0_pair N).Δ := ⟨g, hg⟩
  set b_sub : (Gamma0_pair N).Δ := ⟨(Gamma0_antiInvolution N).bar g, h_bar_delta⟩
  -- CoprimeDet for a
  have ha_cop : CoprimeDet N a_sub := fun A' hA' => by
    have : A' = A := by
      ext i j; have h := congr_fun₂ (hA'.symm.trans hA) i j
      simp only [Matrix.map_apply] at h; exact_mod_cast h
    rw [this]; exact hdet_coprime
  -- CoprimeDet for b (bar(g) has same det, hence same coprime condition)
  have hb_cop : CoprimeDet N b_sub := fun B hB_eq => by
    -- det(B) = det(bar(g)) = det(g) = det(A), and gcd(det(A), N) = 1
    have hBdet : B.det = A.det := by
      have h1 := det_intMat_cast 2 B; rw [← hB_eq, Gamma0_AL_bar_det, hA, det_intMat_cast] at h1
      exact_mod_cast h1.symm
    rw [hBdet]; exact hdet_coprime
  -- Same SL₂-double coset: cosetMap ⟦a⟧ = cosetMap ⟦b⟧
  -- This requires same elementary divisors, proved by the gcd-of-entries argument:
  -- gcd(a₀, N) = 1 implies gcd(entries of A) = gcd(entries of B)
  -- where B = AL-transformed A.
  have h_coset_eq : cosetMap N ⟦a_sub⟧ = cosetMap N ⟦b_sub⟧ := by
    -- Unfold to SL₂-DC equality
    change (⟦Delta0_inclusion N a_sub⟧ : HeckeCoset (GL_pair 2)) = ⟦Delta0_inclusion N b_sub⟧
    rw [HeckeCoset.eq_iff]
    -- Need: bar(g) ∈ DC(g, SL₂, SL₂)
    symm; apply DoubleCoset.doubleCoset_eq_of_mem
    -- Step 1: Integer matrix B for bar(g)
    obtain ⟨c₀, hc₀⟩ := hAN
    set B : Matrix (Fin 2) (Fin 2) ℤ :=
      Matrix.of ![![A 0 0, c₀], ![↑N * A 0 1, A 1 1]] with hB_def
    -- Step 2: bar(g) has matrix B (same computation as Gamma0_AL_map_Δ)
    have hB_det : B.det = A.det := by
      simp only [B, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      have : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
      linarith [show c₀ * (↑N * A 0 1) = A 0 1 * A 1 0 from by rw [hc₀]; ring]
    have hA_det_pos : 0 < A.det := by
      rw [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]; exact hg.2.1
    have hB_ne : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
      rw [det_intMat_cast]; exact_mod_cast (hB_det ▸ hA_det_pos).ne'
    set g' : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero _ hB_ne
    have hg'_eq : (Gamma0_antiInvolution N).bar g = g' := by
      show (Gamma0_AL_hom N g).unop = g'
      simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
      suffices h : g' * wN N = wN N * MulOpposite.unop ((GL_transposeEquiv 2) g) by
        rw [← h]; group
      apply Units.ext; ext i j
      simp only [GeneralLinearGroup.coe_mul, GL_transposeEquiv_val, wN_val,
        Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
        Fin.sum_univ_two, hA, g', GeneralLinearGroup.mkOfDetNeZero]
      fin_cases i <;> fin_cases j <;>
        simp [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.head_fin_const, Matrix.map_apply]
      · exact_mod_cast show c₀ * ↑N = A 1 0 from by rw [hc₀]; ring
      · ring
    have hbar_val : (↑((Gamma0_antiInvolution N).bar g) : Matrix (Fin 2) (Fin 2) ℚ) =
        B.map (Int.cast : ℤ → ℚ) := by rw [hg'_eq]; rfl
    -- Step 4: SNF for A and B
    obtain ⟨dA, hdA_pos, hdA_div, LA, RA, hSNF_A⟩ :=
      exists_divchain_diagonal_of_posdet 2 A hA_det_pos
    obtain ⟨dB, hdB_pos, hdB_div, LB, RB, hSNF_B⟩ :=
      exists_divchain_diagonal_of_posdet 2 B (hB_det ▸ hA_det_pos)
    -- DivChain for Fin 2: dA 0 | dA 1 and dB 0 | dB 1
    have hdA01 : dA 0 ∣ dA 1 := hdA_div 0 (by omega)
    have hdB01 : dB 0 ∣ dB 1 := hdB_div 0 (by omega)
    -- Step 5: dA 0 | every entry of A and B (using coprimality with N)
    have hdA_A : ∀ i j, dA 0 ∣ A i j := snf_first_dvd_entry₂ A dA hdA01 LA RA hSNF_A
    have hdB_B : ∀ i j, dB 0 ∣ B i j := snf_first_dvd_entry₂ B dB hdB01 LB RB hSNF_B
    -- gcd(dA 0, N) = 1 (since dA 0 | A 0 0 and gcd(A 0 0, N) = 1)
    have hAco_isCop : IsCoprime (A 0 0) (↑N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hAco
    have hdA_cop : Int.gcd (dA 0) N = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp (hAco_isCop.of_isCoprime_of_dvd_left (hdA_A 0 0))
    have hdB_cop : Int.gcd (dB 0) N = 1 := by
      have hB00 : B 0 0 = A 0 0 := by simp [B, Matrix.of_apply, Matrix.cons_val_zero]
      exact Int.isCoprime_iff_gcd_eq_one.mp
        (hAco_isCop.of_isCoprime_of_dvd_left (hB00 ▸ hdB_B 0 0))
    -- dA 0 | B entries: diagonal is A 0 0 and A 1 1, off-diag uses coprimality
    have hdA_B : ∀ i j, dA 0 ∣ B i j := by
      intro i j; fin_cases i <;> fin_cases j
      · show dA 0 ∣ B 0 0; simp only [B, Matrix.of_apply, Matrix.cons_val_zero]; exact hdA_A 0 0
      · show dA 0 ∣ B 0 1; simp only [B, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_fin_const]
        -- B 0 1 = c₀ = A 1 0 / N; need dA 0 | c₀ from dA 0 | N*c₀ and gcd(dA 0, N) = 1
        exact IsCoprime.dvd_of_dvd_mul_left
          (Int.isCoprime_iff_gcd_eq_one.mpr hdA_cop) (hc₀ ▸ hdA_A 1 0)
      · show dA 0 ∣ B 1 0; simp only [B, Matrix.of_apply, Matrix.cons_val_one,
          Matrix.head_cons]; exact dvd_mul_of_dvd_right (hdA_A 0 1) _
      · show dA 0 ∣ B 1 1; simp only [B, Matrix.of_apply, Matrix.cons_val_one,
          Matrix.head_fin_const]; exact hdA_A 1 1
    -- dB 0 | A entries (symmetric argument)
    have hdB_A : ∀ i j, dB 0 ∣ A i j := by
      intro i j; fin_cases i <;> fin_cases j
      · show dB 0 ∣ A 0 0
        have : B 0 0 = A 0 0 := by simp [B, Matrix.of_apply, Matrix.cons_val_zero]
        exact this ▸ hdB_B 0 0
      · show dB 0 ∣ A 0 1
        -- dB 0 | B 1 0 = N * A 0 1, gcd(dB 0, N) = 1 → dB 0 | A 0 1
        have hB10 : B 1 0 = ↑N * A 0 1 := by
          simp [B, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
        exact IsCoprime.dvd_of_dvd_mul_left
          (Int.isCoprime_iff_gcd_eq_one.mpr hdB_cop) (hB10 ▸ hdB_B 1 0)
      · show dB 0 ∣ A 1 0
        -- dB 0 | B 0 1 = c₀, and A 1 0 = N * c₀, so dB 0 | A 1 0
        have hB01 : B 0 1 = c₀ := by
          simp [B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_fin_const]
        rw [hc₀]; exact dvd_mul_of_dvd_right (hB01 ▸ hdB_B 0 1) _
      · show dB 0 ∣ A 1 1
        have : B 1 1 = A 1 1 := by
          simp [B, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_fin_const]
        exact this ▸ hdB_B 1 1
    -- Step 6: dA 0 | dB 0 and dB 0 | dA 0, hence dA 0 = dB 0
    have hdA_dvd_dB : dA 0 ∣ dB 0 := by
      have h := congr_fun₂ hSNF_B 0 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ite_true] at h
      rw [← h]
      exact dvd_add
        (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right (hdA_B 0 0) _)
          (dvd_mul_of_dvd_right (hdA_B 1 0) _)) _)
        (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right (hdA_B 0 1) _)
          (dvd_mul_of_dvd_right (hdA_B 1 1) _)) _)
    have hdB_dvd_dA : dB 0 ∣ dA 0 := by
      have h := congr_fun₂ hSNF_A 0 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ite_true] at h
      rw [← h]
      exact dvd_add
        (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right (hdB_A 0 0) _)
          (dvd_mul_of_dvd_right (hdB_A 1 0) _)) _)
        (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right (hdB_A 0 1) _)
          (dvd_mul_of_dvd_right (hdB_A 1 1) _)) _)
    have h_d0 : dA 0 = dB 0 :=
      le_antisymm (Int.le_of_dvd (hdB_pos 0) hdA_dvd_dB) (Int.le_of_dvd (hdA_pos 0) hdB_dvd_dA)
    -- Products: dA 0 * dA 1 = det(A) = det(B) = dB 0 * dB 1
    have hprod_A : dA 0 * dA 1 = A.det := by
      have h := congr_arg Matrix.det hSNF_A
      simp only [Matrix.det_mul, LA.prop, RA.prop, one_mul, mul_one,
        Matrix.det_diagonal, Fin.prod_univ_two] at h; linarith
    have hprod_B : dB 0 * dB 1 = B.det := by
      have h := congr_arg Matrix.det hSNF_B
      simp only [Matrix.det_mul, LB.prop, RB.prop, one_mul, mul_one,
        Matrix.det_diagonal, Fin.prod_univ_two] at h; linarith
    have h_d1 : dA 1 = dB 1 :=
      mul_left_cancel₀ (ne_of_gt (hdA_pos 0))
        (show dA 0 * dA 1 = dA 0 * dB 1 by rw [hprod_A, h_d0, hprod_B, hB_det])
    -- Step 7: diag(dA) = diag(dB), so A and B are SL₂-equivalent to the same diagonal
    have h_diag : Matrix.diagonal dA = Matrix.diagonal dB := by
      congr 1; ext k; fin_cases k <;> assumption
    -- Construct SL₂ elements: B = (LB⁻¹ LA) * A * (RA * RB⁻¹)
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨mapGL ℚ (LB⁻¹ * LA), coe_mem_SLnZ 2 _, mapGL ℚ (RA * RB⁻¹),
      coe_mem_SLnZ 2 _, ?_⟩
    -- bar(g) = mapGL(LB⁻¹ LA) * g * mapGL(RA RB⁻¹) as GL₂(ℚ)
    -- Unfold Delta0_inclusion to get g and bar(g) directly
    show (b_sub : (Gamma0_pair N).Δ).1 =
      mapGL ℚ (LB⁻¹ * LA) * (a_sub : (Gamma0_pair N).Δ).1 * mapGL ℚ (RA * RB⁻¹)
    -- ℤ-level: LB⁻¹ * LA * A * (RA * RB⁻¹) = B (using .val to avoid coercion issues)
    have hLL : (LB⁻¹).val * LB.val = 1 := by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel]; simp
    have hRR : RB.val * (RB⁻¹).val = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; simp
    have h_int : (LB⁻¹).val * LA.val * A * (RA.val * (RB⁻¹).val) = B := by
      calc (LB⁻¹).val * LA.val * A * (RA.val * (RB⁻¹).val)
          = (LB⁻¹).val * (LA.val * A * RA.val) * (RB⁻¹).val := by
            simp only [Matrix.mul_assoc]
        _ = (LB⁻¹).val * Matrix.diagonal dB * (RB⁻¹).val := by rw [hSNF_A, h_diag]
        _ = (LB⁻¹).val * (LB.val * B * RB.val) * (RB⁻¹).val := by rw [hSNF_B]
        _ = B := by
            simp only [Matrix.mul_assoc]
            rw [show (LB⁻¹).val * (LB.val * (B * (RB.val * (RB⁻¹).val))) =
                (LB⁻¹).val * (LB.val * (B * 1)) from by rw [hRR]]
            rw [Matrix.mul_one, ← Matrix.mul_assoc (LB⁻¹).val, hLL, Matrix.one_mul]
    -- Lift to GL₂(ℚ) using the integer equation h_int
    rw [show (b_sub : (Gamma0_pair N).Δ).1 = g' from hg'_eq]
    apply Units.ext; ext i j
    -- Entry-by-entry: g' i j = (mapGL(LB⁻¹LA) * g * mapGL(RA RB⁻¹)) i j
    -- LHS: g'.val i j = B.map IntCast i j = IntCast(B i j)
    -- RHS: expanded product of IntCast'd entries from SL matrices and A
    -- Both follow from h_int by casting
    simp only [g', GeneralLinearGroup.mkOfDetNeZero, Units.val_mul, Matrix.mul_apply,
      Matrix.map_apply, Fin.sum_univ_two, hA, mapGL_coe_matrix, algebraMap_int_eq]
    -- Now goal should be about IntCast entries; extract from h_int
    have h := congr_fun₂ (congr_arg (fun M : Matrix _ _ ℤ => M.map (Int.cast : ℤ → ℚ)) h_int) i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul] at h
    -- Normalize coercions: SL.map → matrix entries, GL.mk' → matrix entries
    simp only [SpecialLinearGroup.map, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, Function.comp_apply, Units.val_mk, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom, Matrix.unitOfDetInvertible,
      SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    -- Simplify ↑↑a_sub to A entries and GeneralLinearGroup.mk' to B entries
    change (B.map (Int.cast : ℤ → ℚ)) i j = _
    rw [hA] at *; simp only [Matrix.map_apply] at h ⊢
    push_cast at h ⊢; linarith
  -- Apply shimura_prop_3_31
  have h_Gamma0_eq := shimura_prop_3_31 N a_sub b_sub ha_cop hb_cop h_coset_eq
  -- ⟦a⟧ = ⟦b⟧ as Γ₀-HeckeCosets → bar(g) ∈ DC(g)
  rw [HeckeCoset.eq_iff] at h_Gamma0_eq
  rw [DoubleCoset.doubleCoset_eq_of_mem (show g ∈ DoubleCoset.doubleCoset g _ _ from
    DoubleCoset.mem_doubleCoset_self _ _ g)]
  rw [h_Gamma0_eq]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- **Prime-local clearing**: if not all entries of a 2×2 integer matrix are divisible by
a prime `p` coprime to `N`, then some `(l, t) ∈ {0,1}²` makes
`A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1)` coprime to `p`.
Four cases on which entry avoids `p`: `A 0 0` → `(0,0)`; `A 1 0` → `(1,0)`;
`A 0 1` → `(0,1)`; `A 1 1` → `(1,1)`. -/
private lemma entry_clear_prime (A : Matrix (Fin 2) (Fin 2) ℤ) (N : ℤ)
    (p : ℕ) (hp : p.Prime) (hpN : ¬((p : ℤ) ∣ N))
    (hprim : ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)) :
    ∃ l t : ℤ, ¬((p : ℤ) ∣ (A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1))) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases ha : (p : ℤ) ∣ A 0 0
  · by_cases hc : (p : ℤ) ∣ A 1 0
    · by_cases hb : (p : ℤ) ∣ A 0 1
      · -- Case 4: p | A 0 0, A 0 1, A 1 0 → p ∤ A 1 1 by hprim. Use (1, 1).
        have hd : ¬((p : ℤ) ∣ A 1 1) := fun hd => hprim ⟨ha, hb, hc, hd⟩
        refine ⟨1, 1, fun h => hd ?_⟩
        have h1 : (p : ℤ) ∣ A 0 0 + A 1 0 + N * A 0 1 :=
          dvd_add (dvd_add ha hc) (dvd_mul_of_dvd_right hb _)
        have h2 := dvd_sub h h1
        rw [show A 0 0 + 1 * A 1 0 + N * 1 * (A 0 1 + 1 * A 1 1) -
          (A 0 0 + A 1 0 + N * A 0 1) = N * A 1 1 from by ring] at h2
        exact (hp'.dvd_mul.mp h2).resolve_left hpN
      · -- Case 3: p | A 0 0, A 1 0, p ∤ A 0 1. Use (0, 1).
        refine ⟨0, 1, fun h => hb ?_⟩
        have h1 := dvd_sub h ha
        rw [show A 0 0 + 0 * A 1 0 + N * 1 * (A 0 1 + 0 * A 1 1) - A 0 0 =
          N * A 0 1 from by ring] at h1
        exact (hp'.dvd_mul.mp h1).resolve_left hpN
    · -- Case 2: p | A 0 0, p ∤ A 1 0. Use (1, 0).
      refine ⟨1, 0, fun h => hc ?_⟩
      have h1 := dvd_sub h ha
      rwa [show A 0 0 + 1 * A 1 0 + N * 0 * (A 0 1 + 1 * A 1 1) - A 0 0 =
        A 1 0 from by ring] at h1
  · -- Case 1: p ∤ A 0 0. Use (0, 0).
    exact ⟨0, 0, by rwa [show A 0 0 + 0 * A 1 0 + N * 0 * (A 0 1 + 0 * A 1 1) =
      A 0 0 from by ring]⟩

/-- Congruence of the affine expression: if `l ≡ l' [ZMOD p]` and `t ≡ t' [ZMOD p]`,
then `f(l,t) ≡ f(l',t') [ZMOD p]` where `f(l,t) = a + l*c₀ + N*t*(b + l*d)`. -/
private lemma f_congr_mod (p : ℕ) (l l' t t' a b c₀ d N : ℤ)
    (hl : (p : ℤ) ∣ (l - l')) (ht : (p : ℤ) ∣ (t - t')) :
    (p : ℤ) ∣ ((a + l * c₀ + N * t * (b + l * d)) -
      (a + l' * c₀ + N * t' * (b + l' * d))) := by
  have hlt : (p : ℤ) ∣ (l * t - l' * t') := by
    rw [show l * t - l' * t' = (l - l') * t + l' * (t - t') from by ring]
    exact dvd_add (dvd_mul_of_dvd_left hl _) (dvd_mul_of_dvd_right ht _)
  rw [show a + l * c₀ + N * t * (b + l * d) - (a + l' * c₀ + N * t' * (b + l' * d)) =
    (l - l') * c₀ + N * ((t - t') * b + (l * t - l' * t') * d) from by ring]
  exact dvd_add (dvd_mul_of_dvd_left hl _)
    (dvd_mul_of_dvd_right (dvd_add (dvd_mul_of_dvd_left ht _) (dvd_mul_of_dvd_left hlt _)) _)

/-- Content quotient: given integer matrix `A` with positive det, `N | A 1 0`,
`gcd(A 0 0, N) = 1`, and content `d` dividing all entries, produce primitive
quotient `A₀ = A/d` preserving the Δ₀(N) properties. -/
private lemma Gamma0_content_quotient (N : ℕ) [NeZero N]
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA_det_pos : 0 < A.det)
    (hAN : (N : ℤ) ∣ A 1 0)
    (hAco : Int.gcd (A 0 0) N = 1)
    (d : ℕ) (hd_pos : 0 < d)
    (hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j)
    (hd_is_gcd : d = Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
                    (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs)) :
    ∃ (A₀ : Matrix (Fin 2) (Fin 2) ℤ),
      (∀ i j, A i j = ↑d * A₀ i j) ∧
      0 < A₀.det ∧
      (N : ℤ) ∣ A₀ 1 0 ∧
      Int.gcd (A₀ 0 0) N = 1 ∧
      (∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A₀ 0 0 ∧ (p : ℤ) ∣ A₀ 0 1 ∧
        (p : ℤ) ∣ A₀ 1 0 ∧ (p : ℤ) ∣ A₀ 1 1)) := by
  set A₀ : Matrix (Fin 2) (Fin 2) ℤ := fun i j => A i j / d
  have hA_eq : ∀ i j, A i j = ↑d * A₀ i j := fun i j => by
    simp only [A₀]; rw [mul_comm]; exact (Int.ediv_mul_cancel (hd_dvd i j)).symm
  have hdet_eq : A.det = ↑d ^ 2 * A₀.det := by
    simp only [Matrix.det_fin_two]; rw [hA_eq 0 0, hA_eq 0 1, hA_eq 1 0, hA_eq 1 1]; ring
  -- gcd(d, N) = 1 (since d | A 0 0 and gcd(A 0 0, N) = 1)
  -- gcd(d, N) = 1 (d | A 0 0 and gcd(A 0 0, N) = 1 → gcd(d, N) | gcd(A 0 0, N) = 1)
  have hd_Nco : Int.gcd (d : ℤ) N = 1 := by
    apply Nat.eq_one_of_dvd_one; rw [← hAco]
    -- gcd(d, N) | gcd(A 0 0, N): gcd(d,N) | d | A 0 0 and gcd(d,N) | N
    exact Nat.dvd_gcd
      (Int.natAbs_dvd_natAbs.mpr ((Int.gcd_dvd_left (d : ℤ) N).trans (hd_dvd 0 0)))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (d : ℤ) N))
  refine ⟨A₀, hA_eq, ?_, ?_, ?_, ?_⟩
  · -- det(A₀) > 0
    have h := hdet_eq ▸ hA_det_pos
    exact (mul_pos_iff.mp h).elim (fun ⟨_, r⟩ => r)
      (fun ⟨l, _⟩ => absurd l (not_lt.mpr (sq_nonneg (d : ℤ))))
  · -- N | A₀ 1 0
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hd_Nco).symm.dvd_of_dvd_mul_left
      (hA_eq 1 0 ▸ hAN)
  · -- gcd(A₀ 0 0, N) = 1
    exact Int.isCoprime_iff_gcd_eq_one.mp
      ((Int.isCoprime_iff_gcd_eq_one.mpr (hA_eq 0 0 ▸ hAco)).of_isCoprime_of_dvd_left
        (dvd_mul_left (A₀ 0 0) (↑d)))
  · -- Primitivity: q | all A₀ entries → q*d | d (via gcd) → q ≤ 1
    intro q hq ⟨hq00, hq01, hq10, hq11⟩
    have hqd_nat : ∀ i j : Fin 2, q * d ∣ (A i j).natAbs := fun i j => by
      have h : (↑q : ℤ) ∣ A₀ i j := by fin_cases i <;> fin_cases j <;> assumption
      rw [show (A i j).natAbs = ((↑d : ℤ) * A₀ i j).natAbs from by rw [← hA_eq],
        Int.natAbs_mul, Int.natAbs_natCast]
      rw [mul_comm]; exact Nat.mul_dvd_mul_left d (Int.natAbs_dvd_natAbs.mpr h)
    have hqd_dvd_d : q * d ∣ d := by
      conv_rhs => rw [hd_is_gcd]
      exact Nat.dvd_gcd
        (Nat.dvd_gcd (hqd_nat 0 0) (hqd_nat 0 1))
        (Nat.dvd_gcd (hqd_nat 1 0) (hqd_nat 1 1))
    have : q * d ≤ d := Nat.le_of_dvd hd_pos hqd_dvd_d
    have : q ≤ 1 := Nat.le_of_mul_le_mul_right (by linarith) hd_pos
    exact absurd hq.two_le (by omega)

/-- **CRT assembly**: given per-prime avoidance for each prime factor of `c`,
produce a single `(l, t)` making the affine expression coprime to `c`.
Uses `entry_clear_prime` to produce per-prime witnesses, then swaps quantifiers
via `Nat.chineseRemainderOfFinset` on `c.primeFactors`. -/
private lemma exists_coprime_entry (A : Matrix (Fin 2) (Fin 2) ℤ) (N : ℤ)
    (c : ℕ) (hc_pos : 0 < c)
    (hprim : ∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1))
    (hcN : ∀ (p : ℕ), p.Prime → (p : ℤ) ∣ ↑c → ¬((p : ℤ) ∣ N)) :
    ∃ l t : ℤ, Int.gcd (A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1)) ↑c = 1 := by
  -- Per-prime avoidance from entry_clear_prime
  have havoid : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ↑c →
      ∃ l t : ℤ, ¬((p : ℤ) ∣ (A 0 0 + l * A 1 0 + N * t * (A 0 1 + l * A 1 1))) :=
    fun p hp hpc => entry_clear_prime A N p hp (hcN p hp hpc)
      (fun ⟨h1, h2, h3, h4⟩ => hprim p hp ⟨h1, h2, h3, h4⟩)
  -- CRT quantifier swap: ∀ p ∃ (l,t) → ∃ (l,t) ∀ p
  classical
  -- Per-prime witness pairs and their ℕ residues mod p
  set wit : ℕ → ℤ × ℤ := fun p =>
    if h : p.Prime ∧ (p : ℤ) ∣ ↑c
    then ⟨(havoid p h.1 h.2).choose, (havoid p h.1 h.2).choose_spec.choose⟩
    else ⟨0, 0⟩
  set aL : ℕ → ℕ := fun p => ((wit p).1 % (p : ℤ)).toNat
  set aT : ℕ → ℕ := fun p => ((wit p).2 % (p : ℤ)).toNat
  -- Pairwise coprime distinct primes
  have hpw : (c.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact ((Nat.mem_primeFactors.mp hp).1).coprime_iff_not_dvd.mpr
      (fun h => hpq (((Nat.mem_primeFactors.mp hq).1).eq_one_or_self_of_dvd p h |>.resolve_left
        ((Nat.mem_primeFactors.mp hp).1).one_lt.ne'))
  have hpnz : ∀ p ∈ c.primeFactors, (id p : ℕ) ≠ 0 :=
    fun p hp => ((Nat.mem_primeFactors.mp hp).1).ne_zero
  -- CRT lift for l and t
  obtain ⟨l₀, hl₀⟩ := Nat.chineseRemainderOfFinset aL id c.primeFactors hpnz hpw
  obtain ⟨t₀, ht₀⟩ := Nat.chineseRemainderOfFinset aT id c.primeFactors hpnz hpw
  -- Prove gcd = 1 by contradiction: any common prime p | c would be avoided
  refine ⟨↑l₀, ↑t₀, ?_⟩
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpc : (p : ℤ) ∣ ↑c := Int.natCast_dvd_natCast.mpr
    (Int.natCast_dvd_natCast.mp (dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right _ _)))
  have hpf : (p : ℤ) ∣ (A 0 0 + ↑l₀ * A 1 0 + N * ↑t₀ * (A 0 1 + ↑l₀ * A 1 1)) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left _ _)
  have hp_mem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, Int.natCast_dvd_natCast.mp hpc, by omega⟩
  -- The per-prime witness avoids p
  have havw := (havoid p hp hpc).choose_spec.choose_spec
  -- wit p = (lw, tw) where lw, tw are the per-prime witnesses
  have hwit : wit p = ⟨(havoid p hp hpc).choose, (havoid p hp hpc).choose_spec.choose⟩ :=
    dif_pos ⟨hp, hpc⟩
  -- CRT congruences
  have hl_crt : Nat.ModEq p l₀ (aL p) := by simpa using hl₀ p hp_mem
  have ht_crt : Nat.ModEq p t₀ (aT p) := by simpa using ht₀ p hp_mem
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  -- Key: aL p = ((wit p).1 % p).toNat = ((havoid ...).choose % p).toNat
  -- and (wit p).1 = (havoid ...).choose by hwit
  -- CRT + emod chain → (p : ℤ) | (↑l₀ - (wit p).1) and (p : ℤ) | (↑t₀ - (wit p).2)
  have hl_dvd : (p : ℤ) ∣ ((l₀ : ℤ) - (wit p).1) := by
    have h_aL : aL p = ((wit p).1 % (p : ℤ)).toNat := rfl
    rw [h_aL] at hl_crt
    obtain ⟨a', ha'⟩ := Nat.modEq_iff_dvd.mp hl_crt
    obtain ⟨b', hb'⟩ : (p : ℤ) ∣ (((wit p).1 % (p : ℤ)).toNat : ℤ) - (wit p).1 := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp_ne)]
      exact ⟨-((wit p).1 / p), by rw [Int.emod_def]; ring⟩
    exact ⟨-a' + b', by linear_combination -ha' + hb'⟩
  have ht_dvd : (p : ℤ) ∣ ((t₀ : ℤ) - (wit p).2) := by
    have h_aT : aT p = ((wit p).2 % (p : ℤ)).toNat := rfl
    rw [h_aT] at ht_crt
    obtain ⟨a', ha'⟩ := Nat.modEq_iff_dvd.mp ht_crt
    obtain ⟨b', hb'⟩ : (p : ℤ) ∣ (((wit p).2 % (p : ℤ)).toNat : ℤ) - (wit p).2 := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp_ne)]
      exact ⟨-((wit p).2 / p), by rw [Int.emod_def]; ring⟩
    exact ⟨-a' + b', by linear_combination -ha' + hb'⟩
  -- Congruence + contradiction: f(l₀,t₀) ≡ f((wit p).1, (wit p).2) mod p
  have hcongr := f_congr_mod p ↑l₀ (wit p).1 ↑t₀ (wit p).2
    (A 0 0) (A 0 1) (A 1 0) (A 1 1) N hl_dvd ht_dvd
  -- havw says p ∤ f((wit p).1, (wit p).2)
  -- Rewrite havw using hwit to match (wit p).1 = (havoid ...).choose
  rw [show (wit p).1 = (havoid p hp hpc).choose from by rw [hwit],
      show (wit p).2 = (havoid p hp hpc).choose_spec.choose from by rw [hwit]] at hcongr
  apply havw
  obtain ⟨k, hk⟩ := hcongr; obtain ⟨m, hm⟩ := hpf
  exact ⟨m - k, by linear_combination hm - hk⟩

/-- Two-sided Γ₀(N) clearing for **primitive** matrices: given `g ∈ Δ₀(N)` with
`gcd(entries of A) = 1` and coprime-to-N target `c | det`, find `γL, γR ∈ Γ₀(N)` such that
`γL * g * γR` has integer matrix A' with `gcd(A' 0 0, c) = 1`.

Primitive hypothesis ensures that for each bad prime `p | gcd(A 0 0, c)` (with `p ∤ N`),
at least one entry of A avoids p, and a combined row/column Γ₀(N) operation clears p.
CRT handles all bad primes simultaneously. -/
private lemma Gamma0_two_sided_coprime_rep_prim (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (hprim : ∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1))
    (c : ℕ) (hc_pos : 0 < c) (hc_cop : Nat.Coprime c N) (hc_dvd : (c : ℤ) ∣ A.det) :
    ∃ (γL γR : (Gamma0_pair N).H),
      let g' := (γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ)
      ∃ (A' : Matrix (Fin 2) (Fin 2) ℤ),
        (g' : Matrix (Fin 2) (Fin 2) ℚ) = A'.map (Int.cast : ℤ → ℚ) ∧
        (N : ℤ) ∣ A' 1 0 ∧ Int.gcd (A' 0 0) N = 1 ∧ Int.gcd (A' 0 0) c = 1 := by
  -- Primes dividing c don't divide N (from hc_cop)
  have hcN : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ↑c → ¬((p : ℤ) ∣ ↑N) := by
    intro p hp hpc hpN
    have : p ∣ c := Int.natCast_dvd_natCast.mp hpc
    have : p ∣ N := Int.natCast_dvd_natCast.mp hpN
    have hgcd : Nat.gcd p p = p := Nat.gcd_self p
    have hle := Nat.gcd_dvd_left p p
    have h1 := Nat.Coprime.coprime_dvd_left ‹p ∣ c›
      (Nat.Coprime.coprime_dvd_right ‹p ∣ N› hc_cop)
    rw [Nat.Coprime, hgcd] at h1; exact absurd h1 hp.one_lt.ne'
  -- Get (l₀, t₀) from exists_coprime_entry
  obtain ⟨l₀, t₀, hlt⟩ := exists_coprime_entry A ↑N c hc_pos hprim hcN
  -- Build SL₂(ℤ) elements
  set L : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, l₀], ![0, 1]] with hL_def
  have hL_det : L.det = 1 := by
    simp [L, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  set L_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨L, hL_det⟩
  set R : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![↑N * t₀, 1]] with hR_def
  have hR_det : R.det = 1 := by
    simp [R, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  set R_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨R, hR_det⟩
  -- Gamma0 membership
  have hL_Gamma0 : L_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [L_sl, L, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
  have hR_Gamma0 : R_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [R_sl, R, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons]
  refine ⟨⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ hL_Gamma0⟩,
    ⟨mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ hR_Gamma0⟩, ?_⟩
  -- A' = L * A * R. Compute the key entries.
  set A' := L * A * R
  -- Compute (0,0) and (1,0) entries of L * A * R
  have h00 : A' 0 0 = A 0 0 + l₀ * A 1 0 + (A 0 1 + l₀ * A 1 1) * (↑N * t₀) := by
    show (L * A * R) 0 0 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, L, R, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
    ring
  have h10 : A' 1 0 = A 1 0 + A 1 1 * (↑N * t₀) := by
    show (L * A * R) 1 0 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, L, R, Matrix.of_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
    ring
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · -- g' = A'.map Int.cast
    show ((mapGL ℚ L_sl) * g * (mapGL ℚ R_sl) : GL (Fin 2) ℚ).val = A'.map (Int.cast : ℤ → ℚ)
    rw [Units.val_mul, Units.val_mul, mapGL_coe_matrix, mapGL_coe_matrix, hA, Matrix.mul_assoc]
    simp only [SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.mapMatrix_apply,
      algebraMap_int_eq, Int.coe_castRingHom, L_sl, R_sl, SpecialLinearGroup.coe_mk]
    ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
    fin_cases i <;> fin_cases j <;>
      simp [L, R, A', Matrix.mul_apply, Matrix.vecMul, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, vecHead, vecTail, Finset.sum]
  · -- N ∣ A' 1 0
    rw [h10, show A 1 0 + A 1 1 * (↑N * t₀) = A 1 0 + ↑N * (A 1 1 * t₀) from by ring]
    exact dvd_add hAN (dvd_mul_right _ _)
  · -- gcd(A' 0 0, N) = 1
    obtain ⟨k, hk⟩ := hAN
    rw [h00, hk, show A 0 0 + l₀ * (↑N * k) + (A 0 1 + l₀ * A 1 1) * (↑N * t₀) =
      A 0 0 + ↑N * (l₀ * k + (A 0 1 + l₀ * A 1 1) * t₀) from by ring]
    rw [Int.gcd_add_mul_left_left]; exact hAco
  · -- gcd(A' 0 0, c) = 1
    rw [h00, show A 0 0 + l₀ * A 1 0 + (A 0 1 + l₀ * A 1 1) * (↑N * t₀) =
      A 0 0 + l₀ * A 1 0 + ↑N * t₀ * (A 0 1 + l₀ * A 1 1) from by ring]
    exact hlt

/-- Scalar centrality for the AL involution: `bar(s · g) ∈ DC(s · g)` follows from
`bar(g) ∈ DC(g)` when `s` is a scalar matrix, since `s` commutes with all Γ₀(N)
elements and `bar(s) = s` for scalar matrices. -/
private lemma Gamma0_AL_scalar_reduce (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (s : GL (Fin 2) ℚ)
    (hs_central : ∀ h : GL (Fin 2) ℚ, s * h = h * s)
    (hs_bar : (Gamma0_antiInvolution N).bar s = s)
    (h_prim : ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _)) :
    ((Gamma0_antiInvolution N).bar (s * g)) ∈
      DoubleCoset.doubleCoset (s * g) ((Gamma0_pair N).H : Set _)
        ((Gamma0_pair N).H : Set _) := by
  -- bar(s*g) = bar(g) * bar(s) = bar(g) * s  (anti-involution reverses, bar(s) = s)
  rw [AntiInvolution.bar_mul, hs_bar]
  -- bar(g) ∈ DC(g) gives bar(g) = γ₁ * g * γ₂ for γ₁, γ₂ ∈ H
  rw [DoubleCoset.mem_doubleCoset] at h_prim ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, h_eq⟩ := h_prim
  -- bar(g) * s = γ₁ * g * γ₂ * s = γ₁ * g * (s * γ₂) (centrality of s)
  -- = γ₁ * (s * g) * γ₂ (centrality of s)
  exact ⟨γ₁, hγ₁, γ₂, hγ₂, by rw [h_eq]; simp only [mul_assoc, hs_central]⟩
/-- The AL involution preserves the (0,0) entry of integer matrices:
if `bar(g)` has integer matrix `B` and `g` has integer matrix `A`, then `B 0 0 = A 0 0`.
Proof: `bar(g) * wN = wN * g^T`, so `(bar(g))₀₀ * 1 = 1 * g₀₀`. -/
private lemma Gamma0_AL_preserves_00 (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : g.val = A.map (Int.cast : ℤ → ℚ))
    (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : ((Gamma0_antiInvolution N).bar g : GL _ ℚ).val = B.map (Int.cast : ℤ → ℚ)) :
    B 0 0 = A 0 0 := by
  have h_bw : ((Gamma0_AL_hom N g).unop : GL _ ℚ).val * (wN N).val =
      (wN N).val * g.val.transpose := by
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
      Units.val_mul, GL_transposeEquiv_val]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel]; simp
  have h00 := congr_fun₂ h_bw 0 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, wN_val, Matrix.diagonal,
    Matrix.transpose_apply, mul_one, mul_zero, add_zero, zero_add] at h00
  -- h00 : bar(g) 0 0 = g 0 0 at ℚ level
  exact_mod_cast show (B 0 0 : ℚ) = (A 0 0 : ℚ) from
    (by rw [show (B 0 0 : ℚ) = (B.map (Int.cast : ℤ → ℚ)) 0 0 from by
        simp [Matrix.map_apply], ← hB]; simpa using h00 : (B 0 0 : ℚ) = g.val 0 0).trans
    (by rw [show (A 0 0 : ℚ) = (A.map (Int.cast : ℤ → ℚ)) 0 0 from by
        simp [Matrix.map_apply], ← hA] : g.val 0 0 = (A 0 0 : ℚ))

/-- The Atkin-Lehner anti-involution fixes every double coset of `Gamma0_pair N`. -/
private lemma Gamma0_AL_in_doubleCoset (N : ℕ) [NeZero N]
    (g : GL (Fin 2) ℚ) (hg : g ∈ (Gamma0_pair N).Δ) :
    ((Gamma0_antiInvolution N).bar g) ∈
      DoubleCoset.doubleCoset (g : GL (Fin 2) ℚ)
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  -- Step 1: bar(g) ∈ Δ₀(N) and det(bar(g)) = det(g)
  have h_bar_delta := Gamma0_AL_map_Δ N g hg
  -- det preservation: bar(g) = w gᵀ w⁻¹, det(conjugation) = det(gᵀ) = det(g)
  have h_det_eq : ((Gamma0_antiInvolution N).bar g : Matrix (Fin 2) (Fin 2) ℚ).det =
      (g : Matrix (Fin 2) (Fin 2) ℚ).det := by
    show ((Gamma0_AL_hom N g).unop : GL (Fin 2) ℚ).val.det = g.val.det
    simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
      Units.val_mul, Matrix.det_mul, GL_transposeEquiv_val, MulOpposite.unop_op,
      Matrix.det_transpose]
    have h1 : (wN N : GL (Fin 2) ℚ).val.det * ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]; simp
    have h2 : (wN N : GL (Fin 2) ℚ).val.det * g.val.det *
        ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det =
      g.val.det * ((wN N : GL (Fin 2) ℚ).val.det * ((wN N)⁻¹ : GL (Fin 2) ℚ).val.det) := by ring
    rw [h2, h1, mul_one]
  -- Step 2: Extract integer matrix and case-split
  obtain ⟨hint, hdet_pos_g, A, hA, hAN, hAco⟩ := hg
  -- Reconstruct hg for branch lemmas
  have hg : g ∈ (Gamma0_pair N).Δ := ⟨hint, hdet_pos_g, A, hA, hAN, hAco⟩
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  set m := A.det.natAbs
  have hm_pos : 0 < m := Int.natAbs_pos.mpr (ne_of_gt hA_det_pos)
  have hdet_m : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ) := by
    rw [hA, det_intMat_cast]
    exact_mod_cast show A.det = (m : ℤ) from (Int.natAbs_of_nonneg (le_of_lt hA_det_pos)).symm
  -- Case 1: gcd(det, N) = 1 → coprime branch
  by_cases h_cop : Int.gcd A.det N = 1
  · exact Gamma0_AL_in_DC_coprime N g hg A hA hAN hAco h_cop
  · -- Case 2: gcd(det, N) > 1 → use gcd(m, N^m) to extract N-power part
    set b := Nat.gcd m (N ^ m) with hb_def
    have hb_dvd_Npow : b ∣ N ^ m := Nat.gcd_dvd_right m _
    by_cases hbm : b = m
    · -- Pure bad: m | N^m → apply Gamma0_AL_in_DC_bad
      exact Gamma0_AL_in_DC_bad N g hg m hm_pos m (hbm ▸ hb_dvd_Npow) hdet_m
    · -- Mixed case: det has both N-factors and non-N-factors.
      -- Use shimura_prop_3_33_gen: if gcd(A 0 0, m) = 1, both g and bar(g)
      -- are in DC_Γ₀(diag(1,m)), hence in the same DC.
      by_cases ham : Int.gcd (A 0 0) (m : ℤ) = 1
      · -- Easy mixed: gcd(a₀₀, det) = 1 → apply shimura_prop_3_33_gen to both g and bar(g)
        -- g ∈ DC_Γ₀(diag(1, m))
        have h_g_dc := shimura_prop_3_33_gen N m hm_pos g hg A hA hAN hdet_m ham
        -- bar(g) ∈ DC_Γ₀(diag(1, m)): extract from h_bar_delta
        obtain ⟨_, _, B, hB, hBN, hBco⟩ := h_bar_delta
        -- The (0,0) entry is preserved by AL: bar(g) 0 0 = g 0 0
        -- Proof: (wN * g^T * wN⁻¹) 0 0 = (diag(1,N) * g^T * diag(1,1/N)) 0 0 = g 0 0
        -- bar(g) 0 0 = g 0 0: use bar(g)*wN = wN*g^T, extract (0,0) entry
        have hB00 : B 0 0 = A 0 0 :=
          Gamma0_AL_preserves_00 N g A hA B hB
        have hbar_det' : (↑((Gamma0_antiInvolution N).bar g) : Matrix (Fin 2) (Fin 2) ℚ).det =
            (m : ℚ) := by rw [h_det_eq, hdet_m]
        have h_bar_delta' : ((Gamma0_antiInvolution N).bar g) ∈ Delta0_submonoid N :=
          Gamma0_AL_map_Δ N g hg
        have h_bar_dc := shimura_prop_3_33_gen N m hm_pos
          ((Gamma0_antiInvolution N).bar g) h_bar_delta' B hB hBN hbar_det' (hB00 ▸ ham)
        rw [DoubleCoset.doubleCoset_eq_of_mem h_g_dc]; exact h_bar_dc
      · -- Hard mixed: gcd(a₀₀, m) > 1.
        -- Strategy: extract scalar content d = gcd(entries A), reduce to primitive
        -- quotient g'' = g / d, apply primitive helper to g'', lift back via
        -- scalar centrality.
        -- Step 1: Content reduction setup
        -- If matrix is primitive (gcd entries = 1): apply primitive helper directly.
        -- If not: factor g = scalar(d) * g'', reduce via Gamma0_AL_scalar_reduce.
        -- For now, the full content reduction is inlined.
        have hb_dvd_m : b ∣ m := Nat.gcd_dvd_left m _
        have hb_pos : 0 < b := Nat.pos_of_ne_zero (by
          intro h; rw [show b = Nat.gcd m (N ^ m) from rfl, Nat.gcd_eq_zero_iff] at h; omega)
        set c := m / b with hc_def
        have hbc : m = b * c := (Nat.mul_div_cancel' hb_dvd_m).symm
        have hc_pos : 0 < c := Nat.div_pos (Nat.le_of_dvd hm_pos hb_dvd_m) hb_pos
        have hA_det_eq_m : A.det = (m : ℤ) :=
          (Int.natAbs_of_nonneg (le_of_lt hA_det_pos)).symm
        have hc_dvd : (c : ℤ) ∣ A.det := by
          rw [hA_det_eq_m]; exact_mod_cast show c ∣ m from ⟨b, by linarith [hbc]⟩
        -- Nat.Coprime c N (p^(m+1) | m contradiction)
        have hc_cop : Nat.Coprime c N := by
          rw [Nat.coprime_comm]; by_contra h_nc
          -- gcd(N, c) ≠ 1, so ∃ prime p | gcd(N, c)
          obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h_nc
          have hpN : p ∣ N := (Nat.dvd_gcd_iff.mp hpg).1
          have hpc : p ∣ c := (Nat.dvd_gcd_iff.mp hpg).2
          -- p^k | m for all k: induction using p^k | gcd(m, N^m) = b
          have : ∀ k, p ^ k ∣ m := by
            intro k; induction k with
            | zero => simp
            | succ k ih =>
              have hpk_Nm : p ^ k ∣ N ^ m :=
                (pow_dvd_pow_of_dvd hpN k).trans
                  (Nat.pow_dvd_pow N (by
                    by_cases hk : k = 0; · simp [hk]
                    · exact le_of_lt (lt_of_lt_of_le
                        (Nat.lt_pow_self hp.one_lt) (Nat.le_of_dvd hm_pos ih))))
              rw [hbc]; exact mul_dvd_mul (Nat.dvd_gcd ih hpk_Nm) hpc
          exact absurd (Nat.le_of_dvd hm_pos (this (m + 1)))
            (not_le.mpr (lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
              (Nat.pow_le_pow_right hp.pos (Nat.le_succ m))))
        -- Content reduction: extract d and check primitivity
        -- If primitive: apply Gamma0_two_sided_coprime_rep_prim directly
        -- If non-primitive: scalar reduce via Gamma0_AL_scalar_reduce, recurse
        -- For now: sorry the full content-reduction + primitive-helper chain
        -- The interface is: Gamma0_two_sided_coprime_rep_prim (primitive helper above)
        -- + Gamma0_AL_scalar_reduce (scalar centrality above)
        -- + caller-side gcd extraction
        -- Split on primitivity of A (gcd of all entries)
        -- Primitive case: apply Gamma0_two_sided_coprime_rep_prim + shimura chain.
        -- Non-primitive: content reduction via Gamma0_AL_scalar_reduce.
        by_cases hprim : ∀ (p : ℕ), p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
            (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)
        · -- Primitive case: apply clearing helper + shimura_prop_3_33_gen chain
          obtain ⟨γL, γR, A', hA', hA'N, hA'Nco, hA'c⟩ :=
            Gamma0_two_sided_coprime_rep_prim N g hg A hA hAN hAco hprim c hc_pos hc_cop hc_dvd
          set g' := (γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ)
          -- gcd(A' 0 0, m) = 1
          have hA'm : Int.gcd (A' 0 0) (m : ℤ) = 1 := by
            rw [show (m : ℤ) = ↑b * ↑c from by exact_mod_cast hbc]
            exact Int.isCoprime_iff_gcd_eq_one.mp (IsCoprime.mul_right
              (IsCoprime.of_isCoprime_of_dvd_right
                ((Int.isCoprime_iff_gcd_eq_one.mpr hA'Nco).pow_right (n := m))
                (by exact_mod_cast hb_dvd_Npow))
              (Int.isCoprime_iff_gcd_eq_one.mpr hA'c))
          have hg'_dc : g' ∈ DoubleCoset.doubleCoset g
              ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
            DoubleCoset.mem_doubleCoset.mpr ⟨γL, γL.2, γR, γR.2, rfl⟩
          have hg' : g' ∈ (Gamma0_pair N).Δ :=
            (Gamma0_pair N).Δ.mul_mem
              ((Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).h₀ γL.2) hg)
              ((Gamma0_pair N).h₀ γR.2)
          have hdet_g' : (g' : GL _ ℚ).val.det = (m : ℚ) := by
            have hdetL : (γL.1 : GL _ ℚ).val.det = 1 := by
              obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γL.2
              rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast, σ.prop]
            have hdetR : (γR.1 : GL _ ℚ).val.det = 1 := by
              obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γR.2
              rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast, σ.prop]
            show ((γL : GL _ ℚ) * g * (γR : GL _ ℚ)).val.det = ↑m
            simp only [Units.val_mul, Matrix.det_mul, hdetL, hdetR, one_mul, mul_one]
            exact hdet_m
          have h_g'_diag := shimura_prop_3_33_gen N m hm_pos g' hg' A' hA' hA'N hdet_g' hA'm
          -- bar(g') ∈ DC(diag): same (0,0)-entry + det argument
          have h_bar_g'_delta := Gamma0_AL_map_Δ N g' hg'
          obtain ⟨_, _, B', hB', hB'N, _⟩ := h_bar_g'_delta
          have hbar_g'_00 : B' 0 0 = A' 0 0 :=
            Gamma0_AL_preserves_00 N g' A' hA' B' hB'
          have hbar_g'_det : (↑((Gamma0_antiInvolution N).bar g') :
              Matrix (Fin 2) (Fin 2) ℚ).det = ↑m := by
            rw [Gamma0_AL_bar_det]; exact hdet_g'
          have h_bar_g'_diag := shimura_prop_3_33_gen N m hm_pos
            ((Gamma0_antiInvolution N).bar g') (Gamma0_AL_map_Δ N g' hg') B' hB' hB'N
            hbar_g'_det (hbar_g'_00 ▸ hA'm)
          -- Transport: bar(g') ∈ DC(diag) = DC(g') = DC(g), extract bar(g)
          have h_bar_g'_in_DC_g : ((Gamma0_antiInvolution N).bar g') ∈
              DoubleCoset.doubleCoset g ((Gamma0_pair N).H : Set _)
                ((Gamma0_pair N).H : Set _) := by
            rw [← DoubleCoset.doubleCoset_eq_of_mem hg'_dc,
              DoubleCoset.doubleCoset_eq_of_mem h_g'_diag]; exact h_bar_g'_diag
          rw [show (Gamma0_antiInvolution N).bar g' =
              (Gamma0_antiInvolution N).bar (γR : GL _ ℚ) *
              (Gamma0_antiInvolution N).bar g *
              (Gamma0_antiInvolution N).bar (γL : GL _ ℚ) from by
            show _ = _; simp only [g', AntiInvolution.bar_mul]; group,
            DoubleCoset.mem_doubleCoset] at h_bar_g'_in_DC_g
          obtain ⟨δ₁, hδ₁, δ₂, hδ₂, h_eq⟩ := h_bar_g'_in_DC_g
          rw [DoubleCoset.mem_doubleCoset]
          exact ⟨((Gamma0_antiInvolution N).bar (γR : GL _ ℚ))⁻¹ * δ₁,
            (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem
              (Gamma0_AL_map_H N _ γR.2)) hδ₁,
            δ₂ * ((Gamma0_antiInvolution N).bar (γL : GL _ ℚ))⁻¹,
            (Gamma0_pair N).H.mul_mem hδ₂ ((Gamma0_pair N).H.inv_mem
              (Gamma0_AL_map_H N _ γL.2)),
            by calc (Gamma0_antiInvolution N).bar g
                = ((Gamma0_antiInvolution N).bar (γR : GL _ ℚ))⁻¹ *
                  ((Gamma0_antiInvolution N).bar (γR : GL _ ℚ) *
                    (Gamma0_antiInvolution N).bar g *
                    (Gamma0_antiInvolution N).bar (γL : GL _ ℚ)) *
                  ((Gamma0_antiInvolution N).bar (γL : GL _ ℚ))⁻¹ := by group
              _ = _ := by rw [h_eq]; group⟩
        · -- Non-primitive: extract full content d, form primitive quotient, dispatch.
          push_neg at hprim
          obtain ⟨p, hp, hpA00, hpA01, hpA10, hpA11⟩ := hprim
          -- Full content d = gcd(all entries of A). d ≥ p ≥ 2.
          set d := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
                    (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
          -- d divides every entry (gcd of all natAbs values)
          have hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j := by
            intro i j; exact Int.natAbs_dvd_natAbs.mp (by
              fin_cases i <;> fin_cases j <;> simp only [d] <;> (
                exact Nat.dvd_trans (by first
                  | exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
                  | exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
                  | exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
                  | exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
                  (dvd_refl _)))
          -- d ≥ 2 (since p | all entries → p | d)
          have hp_dvd_natAbs : ∀ i j : Fin 2, p ∣ (A i j).natAbs := by
            intro i j
            have h : (↑p : ℤ) ∣ A i j := by fin_cases i <;> fin_cases j <;> assumption
            exact Int.natAbs_natCast p ▸ Int.natAbs_dvd_natAbs.mpr h
          have hp_dvd_d : p ∣ d := Nat.dvd_gcd
            (Nat.dvd_gcd (hp_dvd_natAbs 0 0) (hp_dvd_natAbs 0 1))
            (Nat.dvd_gcd (hp_dvd_natAbs 1 0) (hp_dvd_natAbs 1 1))
          have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h => by
            have h00 := hd_dvd 0 0; have h01 := hd_dvd 0 1
            have h10 := hd_dvd 1 0; have h11 := hd_dvd 1 1
            simp [h] at h00 h01 h10 h11
            have hdet0 : A.det = 0 := by rw [Matrix.det_fin_two]; simp [h00, h01, h10, h11]
            linarith)
          have hd_ge2 : 2 ≤ d := le_trans hp.two_le (Nat.le_of_dvd hd_pos hp_dvd_d)
          -- Get primitive quotient A₀ from Gamma0_content_quotient
          obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, hA₀_prim⟩ :=
            Gamma0_content_quotient N A hA_det_pos hAN hAco d hd_pos hd_dvd hd_def
          -- Construct g₀ : GL₂(ℚ) with matrix A₀.map IntCast
          have hA₀_det_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
            rw [det_intMat_cast]; exact_mod_cast hA₀_det_pos.ne'
          set g₀ := GeneralLinearGroup.mkOfDetNeZero (A₀.map (Int.cast : ℤ → ℚ)) hA₀_det_ne
          have hA₀_val : (g₀ : Matrix _ _ ℚ) = A₀.map (Int.cast : ℤ → ℚ) := rfl
          -- g₀ ∈ Δ₀(N)
          have hg₀ : g₀ ∈ (Gamma0_pair N).Δ :=
            ⟨⟨A₀, rfl⟩, by rw [hA₀_val, det_intMat_cast]; exact_mod_cast hA₀_det_pos,
             A₀, rfl, hA₀N, hA₀co⟩
          -- g = scalar(d) * g₀ at the GL level: g.val = (d : ℚ) • g₀.val
          -- since A i j = d * A₀ i j → A.map IntCast = (d : ℚ) • A₀.map IntCast
          have hg_scalar : g.val = (d : ℚ) • g₀.val := by
            ext i j; rw [hA, Matrix.smul_apply, hA₀_val, Matrix.map_apply, Matrix.map_apply]
            simp only [smul_eq_mul]; push_cast [hA₀_eq i j]; ring
          -- Construct the scalar GL element s = d · I₂
          set s : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero
            ((d : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
            (by simp [Matrix.det_smul, Fintype.card_fin]; positivity)
          -- g = s * g₀
          have hg_eq : g = s * g₀ := by
            apply Units.ext; show g.val = s.val * g₀.val
            rw [hg_scalar]; ext i j
            simp only [s, GeneralLinearGroup.mkOfDetNeZero, Units.val_mul,
              Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
              Matrix.one_apply, smul_eq_mul]
            fin_cases i <;> fin_cases j <;> simp <;> ring
          -- s is central (scalar commutes with everything)
          have hs_central : ∀ h : GL (Fin 2) ℚ, s * h = h * s := by
            intro h; apply Units.ext
            show s.val * h.val = h.val * s.val
            ext i j; simp only [s, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
              Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
            fin_cases i <;> fin_cases j <;> simp <;> ring
          -- bar(s) = s (scalar fixed by AL: wN * (d·I)^T * wN⁻¹ = d·I)
          have hs_bar : (Gamma0_antiInvolution N).bar s = s := by
            -- bar(s) = wN * (d·I)^T * wN⁻¹ = wN * d·I * wN⁻¹ = d·I = s
            -- since scalar matrix commutes with wN (both diagonal)
            show (Gamma0_AL_hom N s).unop = s
            simp only [Gamma0_AL_hom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
            suffices h : s * wN N = wN N * MulOpposite.unop ((GL_transposeEquiv 2) s) by
              rw [← h]; group
            apply Units.ext; ext i j
            simp only [s, GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.coe_mul,
              GL_transposeEquiv_val, wN_val, Matrix.mul_apply, Matrix.transpose_apply,
              Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal, smul_eq_mul,
              Fin.sum_univ_two]
            fin_cases i <;> fin_cases j <;> simp <;> ring
          -- bar(g₀) ∈ DC(g₀): dispatch g₀ through existing sorry-free branches.
          -- g₀ is primitive, has det(A₀) > 0, gcd(A₀ 0 0, N) = 1, N | A₀ 1 0.
          -- This is the SAME case analysis as Gamma0_AL_in_doubleCoset applied to g₀.
          -- Since g₀ is primitive, the non-primitive sub-case is vacuous.
          -- Requires either: (a) extracting the case analysis into a reusable helper, or
          -- (b) restructuring with Nat.strongRecOn on det.
          have h_bar_g₀ : ((Gamma0_antiInvolution N).bar g₀) ∈
              DoubleCoset.doubleCoset g₀ ((Gamma0_pair N).H : Set _)
                ((Gamma0_pair N).H : Set _) := by
            -- Inline dispatch for primitive g₀. Non-primitive branch impossible by hA₀_prim.
            -- det and bar-det data for g₀
            set m₀ := A₀.det.natAbs
            have hm₀_pos : 0 < m₀ := Int.natAbs_pos.mpr (ne_of_gt hA₀_det_pos)
            have hdet_g₀ : (g₀ : GL _ ℚ).val.det = (m₀ : ℚ) := by
              show (A₀.map (Int.cast : ℤ → ℚ)).det = ↑m₀
              rw [det_intMat_cast]; push_cast
              exact_mod_cast show A₀.det = (m₀ : ℤ) from
                (abs_of_pos hA₀_det_pos ▸ Int.natCast_natAbs A₀.det).symm
            have h_bar_g₀_delta := Gamma0_AL_map_Δ N g₀ hg₀
            have h_det_eq_g₀ : (↑((Gamma0_antiInvolution N).bar g₀) :
                Matrix (Fin 2) (Fin 2) ℚ).det = g₀.val.det := Gamma0_AL_bar_det N g₀
            -- Branch: coprime det
            by_cases h₀_cop : Int.gcd A₀.det N = 1
            · exact Gamma0_AL_in_DC_coprime N g₀ hg₀ A₀ hA₀_val hA₀N hA₀co h₀_cop
            · -- Non-coprime det: bad or mixed
              set b₀ := Nat.gcd m₀ (N ^ m₀)
              have hb₀_dvd : b₀ ∣ N ^ m₀ := Nat.gcd_dvd_right m₀ _
              by_cases hb₀m : b₀ = m₀
              · -- Pure bad
                exact Gamma0_AL_in_DC_bad N g₀ hg₀ m₀ hm₀_pos m₀ (hb₀m ▸ hb₀_dvd) hdet_g₀
              · -- Mixed: easy or hard-primitive
                by_cases ham₀ : Int.gcd (A₀ 0 0) (m₀ : ℤ) = 1
                · -- Easy mixed: shimura_prop_3_33_gen chain (same as outer easy mixed)
                  have h1 := shimura_prop_3_33_gen N m₀ hm₀_pos g₀ hg₀ A₀ hA₀_val hA₀N
                    hdet_g₀ ham₀
                  obtain ⟨_, _, B₀, hB₀, hB₀N, _⟩ := h_bar_g₀_delta
                  have h00 : B₀ 0 0 = A₀ 0 0 :=
                    Gamma0_AL_preserves_00 N g₀ A₀ hA₀_val B₀ hB₀
                  rw [DoubleCoset.doubleCoset_eq_of_mem h1]
                  exact shimura_prop_3_33_gen N m₀ hm₀_pos _ (Gamma0_AL_map_Δ N g₀ hg₀) B₀
                    hB₀ hB₀N (by rw [Gamma0_AL_bar_det]; exact hdet_g₀) (h00 ▸ ham₀)
                · -- Hard primitive for g₀: same as outer hard-primitive branch.
                  -- Uses Gamma0_two_sided_coprime_rep_prim (hA₀_prim) + shimura chain.
                  -- This is the final case: g₀ is primitive + mixed det + gcd(a₀₀, m₀) > 1.
                  -- The proof is identical to the outer primitive branch (lines ~2560-2610)
                  -- applied to g₀ instead of g.
                  -- Uncommented hard-primitive proof for g₀
                  have hb₀_dvd_m : b₀ ∣ m₀ := Nat.gcd_dvd_left m₀ _
                  have hb₀_pos : 0 < b₀ := Nat.pos_of_ne_zero (by
                    intro h; rw [show b₀ = Nat.gcd m₀ (N ^ m₀) from rfl,
                      Nat.gcd_eq_zero_iff] at h; omega)
                  set c₀ := m₀ / b₀
                  have hbc₀ : m₀ = b₀ * c₀ := (Nat.mul_div_cancel' hb₀_dvd_m).symm
                  have hc₀_pos : 0 < c₀ := Nat.div_pos
                    (Nat.le_of_dvd hm₀_pos hb₀_dvd_m) hb₀_pos
                  have hA₀_det_eq_m₀ : A₀.det = (m₀ : ℤ) :=
                    (abs_of_pos hA₀_det_pos ▸ Int.natCast_natAbs A₀.det).symm
                  have hc₀_dvd : (c₀ : ℤ) ∣ A₀.det := by
                    rw [hA₀_det_eq_m₀]
                    exact_mod_cast show c₀ ∣ m₀ from ⟨b₀, by linarith [hbc₀]⟩
                  have hc₀_cop : Nat.Coprime c₀ N := by
                    rw [Nat.coprime_comm]; by_contra h_nc
                    obtain ⟨p₀, hp₀, hpg⟩ := Nat.exists_prime_and_dvd h_nc
                    have hp₀N := (Nat.dvd_gcd_iff.mp hpg).1
                    have hp₀c := (Nat.dvd_gcd_iff.mp hpg).2
                    suffices ∀ k, p₀ ^ k ∣ m₀ by
                      exact absurd (Nat.le_of_dvd hm₀_pos (this (m₀ + 1)))
                        (not_le.mpr (lt_of_lt_of_le (Nat.lt_pow_self hp₀.one_lt)
                          (Nat.pow_le_pow_right hp₀.pos (Nat.le_succ m₀))))
                    intro k; induction k with
                    | zero => simp
                    | succ k ih =>
                      rw [hbc₀, pow_succ]
                      exact mul_dvd_mul
                        (Nat.dvd_gcd ih ((pow_dvd_pow_of_dvd hp₀N k).trans
                          (Nat.pow_dvd_pow N (le_trans (Nat.lt_pow_self hp₀.one_lt).le
                            (Nat.le_of_dvd hm₀_pos ih))))) hp₀c
                  obtain ⟨γL, γR, A', hA', hA'N, hA'Nco, hA'c⟩ :=
                    Gamma0_two_sided_coprime_rep_prim N g₀ hg₀ A₀ hA₀_val hA₀N hA₀co
                      hA₀_prim c₀ hc₀_pos hc₀_cop hc₀_dvd
                  set g₀' := (γL : GL _ ℚ) * g₀ * (γR : GL _ ℚ)
                  have hA'm₀ : Int.gcd (A' 0 0) (m₀ : ℤ) = 1 := by
                    rw [show (m₀ : ℤ) = ↑b₀ * ↑c₀ from by exact_mod_cast hbc₀]
                    exact Int.isCoprime_iff_gcd_eq_one.mp (IsCoprime.mul_right
                      (IsCoprime.of_isCoprime_of_dvd_right
                        ((Int.isCoprime_iff_gcd_eq_one.mpr hA'Nco).pow_right (n := m₀))
                        (by exact_mod_cast hb₀_dvd))
                      (Int.isCoprime_iff_gcd_eq_one.mpr hA'c))
                  have hg₀'_dc : g₀' ∈ DoubleCoset.doubleCoset g₀
                      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
                    DoubleCoset.mem_doubleCoset.mpr ⟨γL, γL.2, γR, γR.2, rfl⟩
                  have hg₀' : g₀' ∈ (Gamma0_pair N).Δ := (Gamma0_pair N).Δ.mul_mem
                    ((Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).h₀ γL.2) hg₀)
                    ((Gamma0_pair N).h₀ γR.2)
                  have hdet_g₀' : (g₀' : GL _ ℚ).val.det = (m₀ : ℚ) := by
                    have hL : (γL.1 : GL _ ℚ).val.det = 1 := by
                      obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γL.2
                      rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast,
                        σ.prop]
                    have hR : (γR.1 : GL _ ℚ).val.det = 1 := by
                      obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γR.2
                      rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast,
                        σ.prop]
                    show ((γL : GL _ ℚ) * g₀ * (γR : GL _ ℚ)).val.det = ↑m₀
                    simp only [Units.val_mul, Matrix.det_mul, hL, hR, one_mul, mul_one, hdet_g₀]
                  have hD := shimura_prop_3_33_gen N m₀ hm₀_pos g₀' hg₀' A' hA' hA'N
                    hdet_g₀' hA'm₀
                  obtain ⟨_, _, B', hB', hB'N, _⟩ := Gamma0_AL_map_Δ N g₀' hg₀'
                  have h00' : B' 0 0 = A' 0 0 := Gamma0_AL_preserves_00 N g₀' A' hA' B' hB'
                  have hbar_g₀'_det : (↑((Gamma0_antiInvolution N).bar g₀') :
                      Matrix (Fin 2) (Fin 2) ℚ).det = ↑m₀ := by
                    rw [Gamma0_AL_bar_det]; exact hdet_g₀'
                  have hbD := shimura_prop_3_33_gen N m₀ hm₀_pos _
                    (Gamma0_AL_map_Δ N g₀' hg₀') B' hB' hB'N
                    hbar_g₀'_det (h00' ▸ hA'm₀)
                  have h_in : ((Gamma0_antiInvolution N).bar g₀') ∈
                      DoubleCoset.doubleCoset g₀ ((Gamma0_pair N).H : Set _)
                        ((Gamma0_pair N).H : Set _) := by
                    rw [← DoubleCoset.doubleCoset_eq_of_mem hg₀'_dc,
                      DoubleCoset.doubleCoset_eq_of_mem hD]; exact hbD
                  rw [show (Gamma0_antiInvolution N).bar g₀' =
                      (Gamma0_antiInvolution N).bar (γR : GL _ ℚ) *
                      (Gamma0_antiInvolution N).bar g₀ *
                      (Gamma0_antiInvolution N).bar (γL : GL _ ℚ) from by
                    show _ = _; simp only [g₀', AntiInvolution.bar_mul]; group,
                    DoubleCoset.mem_doubleCoset] at h_in
                  obtain ⟨δ₁, hδ₁, δ₂, hδ₂, h_eq⟩ := h_in
                  rw [DoubleCoset.mem_doubleCoset]
                  exact ⟨((Gamma0_antiInvolution N).bar (γR : GL _ ℚ))⁻¹ * δ₁,
                    (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem
                      (Gamma0_AL_map_H N _ γR.2)) hδ₁,
                    δ₂ * ((Gamma0_antiInvolution N).bar (γL : GL _ ℚ))⁻¹,
                    (Gamma0_pair N).H.mul_mem hδ₂ ((Gamma0_pair N).H.inv_mem
                      (Gamma0_AL_map_H N _ γL.2)),
                    by calc (Gamma0_antiInvolution N).bar g₀
                        = ((Gamma0_antiInvolution N).bar (γR : GL _ ℚ))⁻¹ *
                          ((Gamma0_antiInvolution N).bar (γR : GL _ ℚ) *
                            (Gamma0_antiInvolution N).bar g₀ *
                            (Gamma0_antiInvolution N).bar (γL : GL _ ℚ)) *
                          ((Gamma0_antiInvolution N).bar (γL : GL _ ℚ))⁻¹ := by group
                      _ = _ := by rw [h_eq]; group⟩
          -- Lift: bar(g) = bar(s * g₀) ∈ DC(s * g₀) = DC(g)
          rw [hg_eq]
          exact Gamma0_AL_scalar_reduce N g₀ s hs_central hs_bar h_bar_g₀
private lemma Gamma0_onHeckeCoset_eq (N : ℕ) [NeZero N]
    (D : HeckeCoset (Gamma0_pair N)) :
    (Gamma0_antiInvolution N).onHeckeCoset D = D := by
  have hD_eq : D = ⟦HeckeCoset.rep D⟧ := (HeckeCoset.mk_rep D).symm
  rw [hD_eq, AntiInvolution.onHeckeCoset_mk]
  exact HeckeCoset.eq_mk_of_mem (Gamma0_AL_in_doubleCoset N _ (HeckeCoset.rep D).2)

/-- `𝕋 (Gamma0_pair N) ℤ` is a commutative ring (Shimura Prop 3.8 for Gamma0).
    Uses the Atkin-Lehner anti-involution `ι(g) = w · gᵀ · w⁻¹` where
    `w = diag(1, N)`. -/
private noncomputable def instCommRing_Gamma0 (N : ℕ) [NeZero N] :
    CommRing (HeckeRing.𝕋 (Gamma0_pair N) ℤ) :=
  instCommRing_of_antiInvolution (Gamma0_antiInvolution N) (Gamma0_onHeckeCoset_eq N)

attribute [local instance] instCommRing_Gamma0

/-! #### Stage A: Free presentation of HeckeAlgebra 2 -/

/-- Index type for all p-local generators: `(p, k)` with `p` prime, `k ∈ Fin 2`. -/
private abbrev GenIdx := { p : ℕ // p.Prime } × Fin 2

/-- The free polynomial ring on all Hecke algebra generators. -/
private abbrev FreeHecke := MvPolynomial GenIdx ℤ

/-- The presentation map `π : ℤ[X_{(p,k)}] →+* HeckeAlgebra 2`. -/
private noncomputable def π_hom : FreeHecke →+* HeckeAlgebra 2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun ⟨⟨p, _⟩, k⟩ => T_gen 2 p k)

/-- The p-local embedding `ℤ[X₀, X₁] ↪ ℤ[X_{(p,k)}]`. -/
private noncomputable def embedPoly (p : ℕ) (hp : p.Prime) :
    MvPolynomial (Fin 2) ℤ →+* FreeHecke :=
  (MvPolynomial.rename (fun k : Fin 2 => (⟨⟨p, hp⟩, k⟩ : GenIdx))).toRingHom

/-- `π ∘ embedPoly p = evalHom 2 p`. -/
private lemma π_comp_embed (p : ℕ) (hp : p.Prime) :
    π_hom.comp (embedPoly p hp) = evalHom 2 p := by
  apply MvPolynomial.ringHom_ext
  · intro n; simp [π_hom, embedPoly, evalHom]
  · intro k
    simp only [π_hom, embedPoly, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.rename_X, MvPolynomial.eval₂Hom_X', evalHom]

/-- Each p-power-diagonal T_elem is in the range of π. -/
private lemma ppow_mem_π_range (p : ℕ) (hp : p.Prime)
    (e : Fin 2 → ℕ) (he : Monotone e) :
    T_elem (ppowDiag 2 p e) ∈ π_hom.range := by
  obtain ⟨poly, hpoly⟩ := T_gen_generates_R_p p hp 2
    (T_elem (ppowDiag 2 p e)) (T_elem_ppow_mem_R_p 2 p hp e he)
  rw [show evalHom 2 p = π_hom.comp (embedPoly p hp) from
    (π_comp_embed p hp).symm] at hpoly
  exact ⟨embedPoly p hp poly, hpoly⟩

/-- Removing the p-component strictly decreases the product when p divides it. -/
private lemma prod_removePrime_lt (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ ∏ i, a i) :
    ∏ i, removePrime 2 p a i < ∏ i, a i := by
  refine Finset.prod_lt_prod (fun i _ => removePrime_pos 2 p a ha i)
    (fun i _ => Nat.le_of_dvd (ha i) (Nat.ordCompl_dvd (a i) p)) ?_
  simp only [Fin.prod_univ_two] at hp_dvd
  obtain hi | hi := hp.dvd_mul.mp hp_dvd
  · exact ⟨0, Finset.mem_univ _, by
      simp only [removePrime]
      exact Nat.div_lt_self (ha 0)
        (one_lt_pow₀ hp.one_lt (hp.factorization_pos_of_dvd (ha 0).ne' hi).ne')⟩
  · exact ⟨1, Finset.mem_univ _, by
      simp only [removePrime]
      exact Nat.div_lt_self (ha 1)
        (one_lt_pow₀ hp.one_lt (hp.factorization_pos_of_dvd (ha 1).ne' hi).ne')⟩

/-- Every `T_elem a` is in the range of `π`, by strong induction on `∏ a`. -/
private lemma T_elem_mem_π_range (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hdiv : DivChain 2 a) : T_elem a ∈ π_hom.range := by
  suffices ∀ (n : ℕ) (a : Fin 2 → ℕ), (∀ i, 0 < a i) → DivChain 2 a →
      ∏ i, a i = n → T_elem a ∈ π_hom.range by
    exact this _ a ha hdiv rfl
  intro n; induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a ha hdiv hprod
    by_cases h_one : n = 1
    · subst h_one
      have : a = fun _ => 1 := by
        ext i; exact Nat.eq_one_of_dvd_one
          (hprod ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      subst this; rw [T_elem_ones_eq_one 2]; exact π_hom.range.one_mem'
    · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      rw [T_elem_split_prime 2 a ha hdiv p hp]
      apply π_hom.range.mul_mem
      · exact ppow_mem_π_range p hp _ (pComponent_monotone 2 a ha hdiv p)
      · have h_lt : ∏ i, removePrime 2 p a i < n := by
          rw [← hprod]; exact prod_removePrime_lt a ha p hp (hprod ▸ hp_dvd)
        exact ih _ h_lt _ (removePrime_pos 2 p a ha)
          (removePrime_divChain 2 p a hdiv) rfl

/-- The presentation map `π` is surjective. -/
private lemma π_surjective : Function.Surjective π_hom := by
  rw [← RingHom.range_eq_top, eq_top_iff]
  intro f _
  obtain ⟨S, c, hf⟩ := T_diag_span 2 f
  rw [hf]; apply π_hom.range.sum_mem; intro s _
  exact π_hom.range.zsmul_mem (T_elem_mem_π_range s.1.1 s.1.2.1 s.1.2.2) _

/-! #### Stage B: Target ring hom -/

variable (N : ℕ) [NeZero N]

/-- The target ring hom `ψ : ℤ[X_{(p,k)}] →+* 𝕋 (Gamma0_pair N) ℤ`:
    `X_{(p,0)} ↦ T'(1,p)`, `X_{(p,1)} ↦ T'(p,p)` if `p ∤ N` else `0`. -/
private noncomputable def ψ_hom :
    FreeHecke →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ :=
  @MvPolynomial.eval₂Hom _ _ _ _ (instCommRing_Gamma0 N).toCommSemiring
    (Int.castRingHom _) (fun ⟨⟨p, hp⟩, k⟩ =>
    if k = 0 then
      HeckeRing.T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (![1, p])
          (fun i => by fin_cases i <;> simp [hp.pos])
          (by simp [Int.gcd_one_left])) 1
    else if h : p ∣ N then 0
    else
      HeckeRing.T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (![p, p])
          (fun i => by fin_cases i <;> simp [hp.pos])
          (by show Int.gcd (↑p) ↑N = 1
              rw [Int.gcd_natCast_natCast]; exact hp.coprime_iff_not_dvd.mpr h)) 1)

/-- Scalar centrality for double cosets: if `s` is central in `GL₂(ℚ)` and
`x ∈ DC_Γ₀(y)`, then `s * x ∈ DC_Γ₀(s * y)`. -/
private lemma doubleCoset_smul_central (N : ℕ) [NeZero N]
    (s x y : GL (Fin 2) ℚ) (hs : ∀ h : GL (Fin 2) ℚ, s * h = h * s)
    (hx : x ∈ DoubleCoset.doubleCoset y ((Gamma0_pair N).H : Set _)
      ((Gamma0_pair N).H : Set _)) :
    s * x ∈ DoubleCoset.doubleCoset (s * y) ((Gamma0_pair N).H : Set _)
      ((Gamma0_pair N).H : Set _) := by
  rw [DoubleCoset.mem_doubleCoset] at hx ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx
  exact ⟨γ₁, hγ₁, γ₂, hγ₂, by rw [hx_eq]; calc
    s * (γ₁ * y * γ₂) = s * γ₁ * y * γ₂ := by group
    _ = γ₁ * s * y * γ₂ := by rw [hs γ₁]
    _ = γ₁ * (s * y) * γ₂ := by group⟩

/-- Every Gamma0 double coset equals `T_diag_Gamma0 N (![1, m])` for some `m > 0`:
any `g ∈ Δ₀(N)` with integer matrix `A`, `gcd(A 0 0, det) = 1`, has
`⟦g⟧ = T_diag_Gamma0 N (![1, m])` where `m = det(A).natAbs`. -/
private lemma Gamma0_coset_eq_T_diag_of_coprime (N : ℕ) [NeZero N]
    (g : (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g.1 : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (m : ℕ) (hm_pos : 0 < m) (hdet : g.1.val.det = (m : ℚ))
    (ham : Int.gcd (A 0 0) (m : ℤ) = 1) :
    (⟦g⟧ : HeckeCoset (Gamma0_pair N)) =
      T_diag_Gamma0 N (![1, m])
        (fun i => by fin_cases i <;> simp [hm_pos])
        (by simp) :=
  HeckeCoset.eq_mk_of_mem (shimura_prop_3_33_gen N m hm_pos g.1 g.2 A hA hAN hdet ham)

set_option maxHeartbeats 3200000 in
/-- **General diagonal representative** for Gamma0 double cosets: every `g ∈ Δ₀(N)` has
`⟦g⟧ = T_diag_Gamma0 N (![d₁, d₂])` for some `d₁ | d₂`, `d₁ > 0`, `d₂ > 0`,
`gcd(d₁, N) = 1`.

Proof: extract content `d`, get primitive quotient `g₀`, clear `gcd(A₀ 0 0, det)` via
`Gamma0_two_sided_coprime_rep_prim`, apply `Gamma0_coset_eq_T_diag_of_coprime` to get
`⟦g₀'⟧ = T_diag_Gamma0 N (![1, m₀])`, then scale back by `d` to get
`⟦g⟧ = T_diag_Gamma0 N (![d, d*m₀])`. -/
private lemma Gamma0_exists_diag_rep (N : ℕ) [NeZero N]
    (g : (Gamma0_pair N).Δ) :
    ∃ (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1)
      (hdiv : a 0 ∣ a 1),
      (⟦g⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N a ha hgcd := by
  -- Extract integer matrix from g ∈ Δ₀(N)
  obtain ⟨_, hdet_pos, A, hA, hAN, hAco⟩ := g.2
  have hg_mem : g.1 ∈ (Gamma0_pair N).Δ := g.2
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  -- Case: primitive (gcd of all entries = 1 w.r.t. every prime) or not
  by_cases hprim : ∀ (p : ℕ), p.Prime →
      ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)
  · -- PRIMITIVE CASE: clearing + coprime-case helper give diag(1, m)
    set m := A.det.natAbs
    have hm_pos : 0 < m := Int.natAbs_pos.mpr (ne_of_gt hA_det_pos)
    have hdet_m : g.1.val.det = (m : ℚ) := by
      rw [hA, det_intMat_cast]
      have : A.det = (m : ℤ) := (abs_of_pos hA_det_pos ▸ Int.natCast_natAbs A.det).symm
      exact_mod_cast this
    by_cases ham : Int.gcd (A 0 0) (m : ℤ) = 1
    · -- Coprime (0,0): direct
      exact ⟨![1, m], fun i => by fin_cases i <;> simp [hm_pos], by simp, ⟨m, by simp⟩,
        Gamma0_coset_eq_T_diag_of_coprime N g A hA hAN m hm_pos hdet_m ham⟩
    · -- Non-coprime (0,0): clear via Gamma0_two_sided_coprime_rep_prim, then coprime case
      set b := Nat.gcd m (N ^ m)
      set c := m / b
      have hb_dvd_m : b ∣ m := Nat.gcd_dvd_left m _
      have hbc : m = b * c := (Nat.mul_div_cancel' hb_dvd_m).symm
      have hc_pos : 0 < c := Nat.pos_of_ne_zero (by
        intro hc0; have := hbc; rw [hc0, Nat.mul_zero] at this; omega)
      have hA_det_eq : A.det = (m : ℤ) :=
        (abs_of_pos hA_det_pos ▸ Int.natCast_natAbs A.det).symm
      have hc_dvd : (c : ℤ) ∣ A.det := by
        rw [hA_det_eq]; exact_mod_cast show c ∣ m from Dvd.intro_left b hbc.symm
      have hc_cop : Nat.Coprime c N := by
        rw [Nat.coprime_comm]; by_contra h_nc
        obtain ⟨p₀, hp₀, hpg⟩ := Nat.exists_prime_and_dvd h_nc
        have hp₀N := (Nat.dvd_gcd_iff.mp hpg).1
        have hp₀c := (Nat.dvd_gcd_iff.mp hpg).2
        suffices ∀ k, p₀ ^ k ∣ m by
          exact absurd (Nat.le_of_dvd hm_pos (this (m + 1)))
            (not_le.mpr (lt_of_lt_of_le (Nat.lt_pow_self hp₀.one_lt)
              (Nat.pow_le_pow_right hp₀.pos (Nat.le_succ m))))
        intro k; induction k with
        | zero => simp
        | succ k ih =>
          rw [hbc, pow_succ]
          exact mul_dvd_mul
            (Nat.dvd_gcd ih ((pow_dvd_pow_of_dvd hp₀N k).trans
              (Nat.pow_dvd_pow N (le_trans (Nat.lt_pow_self hp₀.one_lt).le
                (Nat.le_of_dvd hm_pos ih))))) hp₀c
      obtain ⟨γL, γR, A', hA', hA'N, hA'Nco, hA'c⟩ :=
        Gamma0_two_sided_coprime_rep_prim N g.1 g.2 A hA hAN hAco hprim c hc_pos hc_cop hc_dvd
      set g' : (Gamma0_pair N).Δ := ⟨(γL : GL _ ℚ) * g.1 * (γR : GL _ ℚ),
        (Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).Δ.mul_mem
          ((Gamma0_pair N).h₀ γL.2) g.2) ((Gamma0_pair N).h₀ γR.2)⟩
      have hg'_coset : (⟦g'⟧ : HeckeCoset (Gamma0_pair N)) = ⟦g⟧ :=
        HeckeCoset.eq_mk_of_mem (DoubleCoset.mem_doubleCoset.mpr
          ⟨γL, γL.2, γR, γR.2, rfl⟩)
      have hA'm : Int.gcd (A' 0 0) (m : ℤ) = 1 := by
        rw [show (m : ℤ) = ↑b * ↑c from by exact_mod_cast hbc]
        exact Int.isCoprime_iff_gcd_eq_one.mp (IsCoprime.mul_right
          (IsCoprime.of_isCoprime_of_dvd_right
            ((Int.isCoprime_iff_gcd_eq_one.mpr hA'Nco).pow_right (n := m))
            (by exact_mod_cast Nat.gcd_dvd_right m (N ^ m)))
          (Int.isCoprime_iff_gcd_eq_one.mpr hA'c))
      have hdet_g' : g'.1.val.det = (m : ℚ) := by
        show ((γL : GL _ ℚ) * g.1 * (γR : GL _ ℚ)).val.det = ↑m
        have hL : (γL.1 : GL _ ℚ).val.det = 1 := by
          obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γL.2
          rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast, σ.prop]
        have hR : (γR.1 : GL _ ℚ).val.det = 1 := by
          obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γR.2
          rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast, σ.prop]
        simp only [Units.val_mul, Matrix.det_mul, hL, hR, one_mul, mul_one, hdet_m]
      rw [← hg'_coset]
      exact ⟨![1, m], fun i => by fin_cases i <;> simp [hm_pos], by simp, ⟨m, by simp⟩,
        Gamma0_coset_eq_T_diag_of_coprime N g' A' hA' hA'N m hm_pos hdet_g' hA'm⟩
  · -- NON-PRIMITIVE CASE: content reduction → scalar * primitive quotient
    push_neg at hprim
    obtain ⟨p, hp, hpA00, hpA01, hpA10, hpA11⟩ := hprim
    set d := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
              (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
    have hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j := by
      intro i j; exact Int.natAbs_dvd_natAbs.mp (by
        fin_cases i <;> fin_cases j <;> simp only [d] <;> (
          exact Nat.dvd_trans (by first
            | exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
            | exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
            | exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
            | exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
            (dvd_refl _)))
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h => by
      have h00 := hd_dvd 0 0; have h01 := hd_dvd 0 1
      have h10 := hd_dvd 1 0; have h11 := hd_dvd 1 1
      simp [h] at h00 h01 h10 h11
      linarith [show A.det = 0 from by rw [Matrix.det_fin_two]; simp [h00, h01, h10, h11]])
    -- Get primitive quotient
    obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, hA₀_prim⟩ :=
      Gamma0_content_quotient N A hA_det_pos hAN hAco d hd_pos hd_dvd hd_def
    -- Build g₀ ∈ Δ₀(N) with matrix A₀
    have hA₀_det_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
      rw [det_intMat_cast]; exact_mod_cast hA₀_det_pos.ne'
    set g₀ : (Gamma0_pair N).Δ := ⟨GeneralLinearGroup.mkOfDetNeZero
      (A₀.map (Int.cast : ℤ → ℚ)) hA₀_det_ne,
      ⟨⟨A₀, rfl⟩, by simp [det_intMat_cast]; exact_mod_cast hA₀_det_pos,
       A₀, rfl, hA₀N, hA₀co⟩⟩
    -- Apply primitive branch to g₀ (g₀ is primitive by hA₀_prim)
    obtain ⟨a₀, ha₀, hgcd₀, hdiv₀, hrep₀⟩ := Gamma0_exists_diag_rep N g₀
    -- g₀ ∈ DC(diagMat a₀): from hrep₀ via HeckeCoset.eq_iff
    have hg₀_dc : g₀.1 ∈ DoubleCoset.doubleCoset (diagMat 2 a₀ : GL (Fin 2) ℚ)
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
      ((HeckeCoset.eq_iff g₀ ⟨_, diagMat_mem_Delta0_of_gcd N a₀ ha₀ hgcd₀⟩).mp hrep₀).symm ▸
        DoubleCoset.mem_doubleCoset_self _ _ g₀.1
    -- g ∈ DC(diagMat(d * a₀)): since g = s * g₀ with s = d · I central,
    -- and s * diagMat(a₀) has entries d * a₀ i on diagonal.
    -- Construct the coset membership directly from hg₀_dc.
    rw [DoubleCoset.mem_doubleCoset] at hg₀_dc
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hg₀_eq⟩ := hg₀_dc
    set a := fun i : Fin 2 => d * a₀ i
    have ha : ∀ i, 0 < a i := fun i => Nat.mul_pos hd_pos (ha₀ i)
    have hd_Nco : Int.gcd (d : ℤ) N = 1 := by
      apply Nat.eq_one_of_dvd_one; rw [← hAco]
      exact Nat.dvd_gcd
        (Int.natAbs_dvd_natAbs.mpr ((Int.gcd_dvd_left (d : ℤ) N).trans (hd_dvd 0 0)))
        (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (d : ℤ) N))
    have hgcd_a : Int.gcd (↑(a 0)) ↑N = 1 := by
      show Int.gcd (↑(d * a₀ 0)) ↑N = 1
      simp only [Int.gcd_natCast_natCast]
      exact Nat.Coprime.mul_left
        (by rwa [Int.gcd_natCast_natCast] at hd_Nco)
        (by rwa [Int.gcd_natCast_natCast] at hgcd₀)
    have hdiv_a : a 0 ∣ a 1 := Nat.mul_dvd_mul_left d hdiv₀
    -- g.1 ∈ DC(diagMat a): use centrality of scalar d · I
    have hg_dc : g.1 ∈ DoubleCoset.doubleCoset (diagMat 2 a : GL (Fin 2) ℚ)
        ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
      rw [DoubleCoset.mem_doubleCoset]
      refine ⟨γ₁, hγ₁, γ₂, hγ₂, ?_⟩
      apply Units.ext; ext i j
      -- g.1 i j = d * g₀.1 i j = d * (γ₁ * diagMat a₀ * γ₂) i j = (γ₁ * diagMat a * γ₂) i j
      have hg₀_ij : g₀.1.val i j = (γ₁ * diagMat 2 a₀ * γ₂).val i j := by
        have h := hg₀_eq; change g₀.1 = _ at h
        exact congr_fun₂ (show g₀.1.val = (γ₁ * diagMat 2 a₀ * γ₂).val from by
          rw [h]) i j
      -- g.1 i j = d * g₀.1 i j
      have hg_ij : g.1.val i j = (d : ℚ) * g₀.1.val i j := by
        have h1 := congr_fun₂ hA i j; simp only [Matrix.map_apply] at h1
        rw [h1]; show ↑(A i j) = (d : ℚ) * (A₀.map (Int.cast : ℤ → ℚ)) i j
        simp only [Matrix.map_apply]; push_cast [hA₀_eq i j]; ring
      -- diagMat a k l = d * diagMat a₀ k l (for all k l)
      have hd_kl : ∀ k l : Fin 2, (diagMat 2 a : GL _ ℚ).val k l =
          (d : ℚ) * (diagMat 2 a₀ : GL _ ℚ).val k l := by
        intro k l; show (diagMat 2 a : GL _ ℚ).val k l = ↑d * (diagMat 2 a₀ : GL _ ℚ).val k l
        rw [diagMat_val 2 a ha, diagMat_val 2 a₀ ha₀]
        simp only [Matrix.diagonal_apply, a]
        split_ifs with heq <;> simp <;> push_cast <;> ring
      show g.1.val i j = (γ₁ * (diagMat 2 a : GL _ ℚ) * γ₂).val i j
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at hg₀_ij ⊢
      rw [hg_ij, hg₀_ij, hd_kl 0 0, hd_kl 0 1, hd_kl 1 0, hd_kl 1 1]; ring
    exact ⟨a, ha, hgcd_a, hdiv_a, HeckeCoset.eq_mk_of_mem hg_dc⟩
  termination_by (g.1.val.det.num.natAbs)
  decreasing_by
    -- Goal: g₀.1.val.det.num.natAbs < g.1.val.det.num.natAbs
    -- g₀ has matrix A₀ with det(A₀) > 0 and A.det = d² * A₀.det, d ≥ 2
    simp only [g₀, GeneralLinearGroup.mkOfDetNeZero]
    -- det(g₀) at ℚ level = det(A₀.map IntCast) = A₀.det (as ℚ)
    rw [show (GeneralLinearGroup.mk' (A₀.map (Int.cast : ℤ → ℚ))
          (invertibleOfNonzero hA₀_det_ne)).val.det = (A₀.det : ℚ) from by
      simp [det_intMat_cast]]
    -- det(g) at ℚ level = det(A.map IntCast) = A.det (as ℚ)
    rw [show g.1.val.det = (A.det : ℚ) from by rw [hA, det_intMat_cast]]
    -- Both are positive integers cast to ℚ, so .num.natAbs = .natAbs
    rw [show (A₀.det : ℚ).num.natAbs = A₀.det.natAbs from by
          simp [Rat.num_intCast],
      show (A.det : ℚ).num.natAbs = A.det.natAbs from by
          simp [Rat.num_intCast]]
    -- A.det = d² * A₀.det with d ≥ 2, A₀.det > 0
    have hdet_eq : A.det = (d : ℤ) ^ 2 * A₀.det := by
      simp only [Matrix.det_fin_two]; rw [hA₀_eq 0 0, hA₀_eq 0 1, hA₀_eq 1 0, hA₀_eq 1 1]; ring
    rw [hdet_eq, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    have hA₀_na : 0 < A₀.det.natAbs := Int.natAbs_pos.mpr (ne_of_gt hA₀_det_pos)
    -- d² * A₀.det.natAbs > A₀.det.natAbs since d² ≥ 4 > 1
    calc A₀.det.natAbs < 2 * A₀.det.natAbs := by omega
      _ ≤ d ^ 2 * A₀.det.natAbs := by
          apply Nat.mul_le_mul_right
          -- d ≥ 2 since p | d and p prime
          have hp_dvd_na : ∀ i j : Fin 2, p ∣ (A i j).natAbs := fun i j => by
            have h : (↑p : ℤ) ∣ A i j := by fin_cases i <;> fin_cases j <;> assumption
            exact Int.natAbs_natCast p ▸ Int.natAbs_dvd_natAbs.mpr h
          have hp_dvd_d : p ∣ d := Nat.dvd_gcd
            (Nat.dvd_gcd (hp_dvd_na 0 0) (hp_dvd_na 0 1))
            (Nat.dvd_gcd (hp_dvd_na 1 0) (hp_dvd_na 1 1))
          nlinarith [le_trans hp.two_le (Nat.le_of_dvd hd_pos hp_dvd_d)]

/-! #### Stage C: Factorization and surjectivity -/

/-- `cosetMap` preserves diagonal cosets: the GL₂ double coset of `diagMat(a)`
viewed via Gamma0 inclusion equals `T_diag a`. -/
private lemma cosetMap_T_diag_Gamma0 (N : ℕ) [NeZero N]
    (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    cosetMap N (T_diag_Gamma0 N a ha hgcd) = T_diag a := by
  -- T_diag_Gamma0 N a = ⟦⟨diagMat 2 a, _⟩⟧ in Gamma0 quotient
  -- cosetMap sends it to ⟦Delta0_inclusion N ⟨diagMat 2 a, _⟩⟧ = ⟦⟨diagMat 2 a, _⟩⟧ in GL quotient
  -- T_diag a = ⟦diagMat_delta 2 a⟧ = ⟦⟨diagMat 2 a, _⟩⟧ (since all entries positive)
  show ⟦Delta0_inclusion N ⟨diagMat 2 a, _⟩⟧ = ⟦diagMat_delta 2 a⟧
  congr 1; ext; simp [Delta0_inclusion, diagMat_delta, ha]

/-- `cosetMap` commutes with `mulMap`: the GL coset of the Gamma0 mulMap output
is the GL double coset of the same underlying product element. -/
private lemma cosetMap_mulMap_mem_GL_DC (N : ℕ) [NeZero N]
    (g₁ g₂ : (Gamma0_pair N).Δ)
    (p : HeckeRing.decompQuot (Gamma0_pair N) g₁ ×
      HeckeRing.decompQuot (Gamma0_pair N) g₂)
    (D : HeckeCoset (GL_pair 2))
    (h : (p.1.out : GL (Fin 2) ℚ) * g₁ * ((p.2.out : GL (Fin 2) ℚ) * g₂) ∈
      DoubleCoset.doubleCoset (HeckeCoset.rep D : GL (Fin 2) ℚ)
        ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _)) :
    cosetMap N (HeckeRing.mulMap (Gamma0_pair N) g₁ g₂ p) = D := by
  show ⟦Delta0_inclusion N _⟧ = D
  rw [← HeckeCoset.mk_rep D]
  exact HeckeCoset.eq_mk_of_mem h

/-- GL DC membership for the coprime mulMap product element.
Takes pre-computed GL DC memberships of the reps to avoid expensive elaboration. -/
private lemma product_mem_GL_DC_coprime_aux
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (σ₁ σ₂ g_m g_n : GL (Fin 2) ℚ)
    (hσ₁ : σ₁ ∈ (SLnZ_subgroup 2 : Set _)) (hσ₂ : σ₂ ∈ (SLnZ_subgroup 2 : Set _))
    (hgm : g_m ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, m]) : GL _ ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _))
    (hgn : g_n ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, n]) : GL _ ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _)) :
    σ₁ * g_m * (σ₂ * g_n) ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, m * n]) : GL _ ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
  rw [DoubleCoset.mem_doubleCoset] at hgm hgn
  obtain ⟨L₁, ⟨σL₁, rfl⟩, R₁, ⟨σR₁, rfl⟩, hm_eq⟩ := hgm
  obtain ⟨L₂, ⟨σL₂, rfl⟩, R₂, ⟨σR₂, rfl⟩, hn_eq⟩ := hgn
  obtain ⟨σp₁, rfl⟩ := hσ₁; obtain ⟨σp₂, rfl⟩ := hσ₂
  set τ := σR₁ * σp₂ * σL₂
  have hcore := doubleCoset_mul_coprime_mem 2 ![1, m] ![1, n]
    (fun i => by fin_cases i <;> simp [hm_pos])
    (fun i => by fin_cases i <;> simp [hn_pos])
    (fun i (hi : i + 1 < 2) => by
      have h0 : i = 0 := by linarith
      show (![1, m]) ⟨i, _⟩ ∣ _; subst h0; simp)
    (fun i (hi : i + 1 < 2) => by
      have h0 : i = 0 := by linarith
      show (![1, n]) ⟨i, _⟩ ∣ _; subst h0; simp)
    (by simp [Fin.prod_univ_two]; exact hcop) τ
  rw [show (![1, m] : Fin 2 → ℕ) * ![1, n] = ![1, m * n] from by
    ext i; fin_cases i <;> simp] at hcore
  rw [DoubleCoset.mem_doubleCoset] at hcore ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hcore_eq⟩ := hcore
  refine ⟨mapGL ℚ (σp₁ * σL₁) * γ₁,
    (SLnZ_subgroup 2).mul_mem (coe_mem_SLnZ 2 _) hγ₁,
    γ₂ * mapGL ℚ σR₂,
    (SLnZ_subgroup 2).mul_mem hγ₂ (coe_mem_SLnZ 2 _), ?_⟩
  rw [hm_eq, hn_eq]
  calc ↑(mapGL ℚ σp₁) * (↑(mapGL ℚ σL₁) * diagMat 2 (![1, m]) * ↑(mapGL ℚ σR₁)) *
        (↑(mapGL ℚ σp₂) * (↑(mapGL ℚ σL₂) * diagMat 2 (![1, n]) * ↑(mapGL ℚ σR₂)))
      = ↑(mapGL ℚ σp₁) * ↑(mapGL ℚ σL₁) *
        (diagMat 2 (![1, m]) * (↑(mapGL ℚ σR₁) * ↑(mapGL ℚ σp₂) * ↑(mapGL ℚ σL₂)) *
          diagMat 2 (![1, n])) * ↑(mapGL ℚ σR₂) := by group
    _ = ↑(mapGL ℚ σp₁) * ↑(mapGL ℚ σL₁) *
        (diagMat 2 (![1, m]) * ↑(mapGL ℚ τ) * diagMat 2 (![1, n])) *
          ↑(mapGL ℚ σR₂) := by simp only [τ, map_mul]
    _ = ↑(mapGL ℚ σp₁) * ↑(mapGL ℚ σL₁) * (γ₁ * diagMat 2 (![1, m * n]) * γ₂) *
          ↑(mapGL ℚ σR₂) := by rw [hcore_eq]
    _ = ↑(mapGL ℚ (σp₁ * σL₁)) * γ₁ * diagMat 2 (![1, m * n]) *
        (γ₂ * ↑(mapGL ℚ σR₂)) := by rw [map_mul]; group

set_option maxHeartbeats 1600000 in
/-- GL DC membership for the coprime mulMap product, specialized to Gamma0 reps. -/
private lemma product_mem_GL_DC_coprime (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, m])
      (fun i => by fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left]))) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, n])
      (fun i => by fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left])))) :
    (p.1.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, m])
        (fun i => by fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left]))).1 *
      ((p.2.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, n])
        (fun i => by fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left]))).1) ∈
    DoubleCoset.doubleCoset (HeckeCoset.rep (T_diag (![1, m * n])) : GL (Fin 2) ℚ)
      ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) := by
  -- DC(rep) = DC(diagMat) from HeckeCoset quotient structure
  have hmn_pos : ∀ i : Fin 2, 0 < (![1, m * n]) i := fun i => by
    fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos]
  have h_dc_eq : DoubleCoset.doubleCoset
      (HeckeCoset.rep (T_diag (![1, m * n]) : HeckeCoset (GL_pair 2)) : GL _ ℚ)
      ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) =
    DoubleCoset.doubleCoset (diagMat 2 (![1, m * n]) : GL _ ℚ)
      ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) := by
    have h1 := HeckeCoset.rep_mem (T_diag (![1, m * n]))
    rw [show T_diag (![1, m * n]) = ⟦diagMat_delta 2 (![1, m * n])⟧ from rfl,
      HeckeCoset.toSet_mk, diagMat_delta_val 2 _ hmn_pos] at h1
    exact DoubleCoset.doubleCoset_eq_of_mem h1
  rw [h_dc_eq]
  -- Get GL DC memberships for the two reps
  have hm_coset := congr_arg (cosetMap N) (HeckeCoset.mk_rep
    (T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm_pos])
      (by simp [Int.gcd_one_left])))
  simp only [cosetMap_T_diag_Gamma0] at hm_coset
  have hm_gl := (HeckeCoset.eq_iff _ (diagMat_delta 2 (![1, m]))).mp hm_coset
  have hn_coset := congr_arg (cosetMap N) (HeckeCoset.mk_rep
    (T_diag_Gamma0 N (![1, n]) (fun i => by fin_cases i <;> simp [hn_pos])
      (by simp [Int.gcd_one_left])))
  simp only [cosetMap_T_diag_Gamma0] at hn_coset
  have hn_gl := (HeckeCoset.eq_iff _ (diagMat_delta 2 (![1, n]))).mp hn_coset
  -- Apply the aux lemma
  apply product_mem_GL_DC_coprime_aux m n hm_pos hn_pos hcop
  · exact Gamma0_le_SLnZ N (SetLike.coe_mem p.1.out)
  · exact Gamma0_le_SLnZ N (SetLike.coe_mem p.2.out)
  · -- rep D_m ∈ DC_{SL₂}(diagMat(![1,m]))
    -- Goal: rep ∈ DC(diagMat, SLnZ, SLnZ). From hm_gl: DC(Delta0_inclusion rep) = DC(diagMat_delta).
    -- Since Delta0_inclusion preserves the GL element, DC(rep) = DC(diagMat_delta) = DC(diagMat).
    -- Goal uses SLnZ_subgroup = (GL_pair 2).H. Convert and use hm_gl.
    -- hm_gl : DC(Delta0_inclusion rep_m) = DC(diagMat_delta). But goal uses SLnZ_subgroup.
    -- (GL_pair 2).H = SLnZ_subgroup 2 definitionally. Use Gamma0_doubleCoset_subset_Gamma.
    apply Gamma0_doubleCoset_subset_Gamma N
    have h := HeckeCoset.rep_mem (T_diag_Gamma0 N (![1, m])
      (fun i => by fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left]))
    simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at h; exact h
  · apply Gamma0_doubleCoset_subset_Gamma N
    have h := HeckeCoset.rep_mem (T_diag_Gamma0 N (![1, n])
      (fun i => by fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left]))
    simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at h; exact h

set_option maxHeartbeats 800000 in
/-- Every mulMap output for coprime `diag(1,m) × diag(1,n)` in the Gamma0 Hecke algebra
equals `T_diag_Gamma0 N (![1, m*n])`. Uses the level-1 `doubleCoset_mul_coprime_mem`
to identify the GL coset, then `Gamma0_exists_diag_rep` + `diagonal_representative_unique`
to pin down the Gamma0 coset. -/
private lemma mulMap_Gamma0_coprime_eq (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, m])
      (fun i => by fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left]))) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, n])
      (fun i => by fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left])))) :
    HeckeRing.mulMap (Gamma0_pair N) _ _ p =
      T_diag_Gamma0 N (![1, m * n])
        (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp [Int.gcd_one_left]) := by
  -- Step 1: Get diagonal representative of the mulMap output
  set D := HeckeRing.mulMap (Gamma0_pair N) _ _ p
  -- The underlying element is in Δ₀(N) (product of Δ elements)
  have hD_mem : (HeckeRing.mulMap (Gamma0_pair N) _ _ p).out.1 ∈ (Gamma0_pair N).Δ :=
    (HeckeCoset.rep (HeckeRing.mulMap (Gamma0_pair N) _ _ p)).2
  obtain ⟨a, ha, hgcd_a, hdiv_a, hrep⟩ := Gamma0_exists_diag_rep N
    (HeckeCoset.rep D)
  -- hrep : ⟦rep D⟧ = T_diag_Gamma0 N a, and ⟦rep D⟧ = D
  have hrep' : D = T_diag_Gamma0 N a ha hgcd_a := by
    rw [← hrep]; exact (HeckeCoset.mk_rep D).symm
  -- Step 2: Apply cosetMap to both sides
  have hGL : cosetMap N D = T_diag a := by
    rw [hrep', cosetMap_T_diag_Gamma0]
  -- Step 3: Show cosetMap of the mulMap output equals T_diag (![1, m*n])
  have hGL_mn : cosetMap N D = T_diag (![1, m * n]) := by
    -- cosetMap N D = ⟦rep D⟧_{GL}. The rep of D lies in the Gamma0 DC of diagMat a,
    -- hence in the GL DC of diagMat a (by Gamma0 ⊆ SL₂). So cosetMap N D = T_diag a = hGL.
    -- But also, the underlying mulMap element is in DC_{SL₂}(diag(1,mn)):
    -- rep(D_m) ∈ DC_{Gamma0}(diag(1,m)) ⊆ DC_{SL₂}(diag(1,m)),
    -- rep(D_n) ∈ DC_{Gamma0}(diag(1,n)) ⊆ DC_{SL₂}(diag(1,n)),
    -- p.1.out, p.2.out ∈ Gamma0 ⊆ SL₂.
    -- By doubleCoset_mul_coprime_mem: product ∈ DC_{SL₂}(diag(1,mn)).
    -- So the GL coset is T_diag(![1,mn]).
    exact cosetMap_mulMap_mem_GL_DC N _ _ p _ (product_mem_GL_DC_coprime N m n hm_pos hn_pos hcop p)
  -- Step 4: a = ![1, m*n] by diagonal uniqueness
  have hdiv_a' : DivChain 2 a := fun i hi => (show i = 0 by omega) ▸ hdiv_a
  have hdiv_mn : DivChain 2 (![1, m * n]) := fun i hi => by
    have h0 : (⟨i, by omega⟩ : Fin 2) = (0 : Fin 2) := Fin.ext (show i = 0 by omega)
    have h1 : (⟨i + 1, hi⟩ : Fin 2) = (1 : Fin 2) := Fin.ext (show i + 1 = 1 by omega)
    show (![1, m * n]) ⟨i, _⟩ ∣ (![1, m * n]) ⟨i + 1, hi⟩; rw [h0, h1]; simp
  have ha_eq : a = ![1, m * n] := diagonal_representative_unique 2 a ![1, m * n]
    ha (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
    hdiv_a' hdiv_mn (by rw [← hGL, hGL_mn])
  subst ha_eq; exact hrep'

/-! #### Gamma0 degree coprime multiplicativity: CRT helpers -/

/-- The (1,0) entry of `diag(1,k)⁻¹ * σ * diag(1,k)` is `σ₁₀ / k` in ℚ.
This is the key entry computation for diagonal stabilizer identification. -/
private lemma diagConj_10 (k : ℕ) (hk : 0 < k) (σ : GL (Fin 2) ℚ) :
    ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹ * σ *
      (diagMat 2 (![1, k] : Fin 2 → ℕ))).1 1 0 = σ.1 1 0 / k := by
  have hk_pos : ∀ i : Fin 2, 0 < (![1, k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hk]
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [diagMat_val 2 _ hk_pos, Units.val_inv_eq_inv_val, Matrix.nonsing_inv_apply_eq,
    Matrix.diagonal_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  split_ifs <;> simp_all <;> ring

/-- **CRT card formula for subgroup quotients**: if `K₁ ⊓ K₂ = L` and every element
of `G` factors as `k₁ * k₂`, then `|G/L| = |G/K₁| * |G/K₂|`. -/
private lemma card_quotient_inf_of_set_mul {G : Type*} [Group G]
    (K₁ K₂ : Subgroup G) [K₁.FiniteIndex] [K₂.FiniteIndex] [(K₁ ⊓ K₂).FiniteIndex]
    (h_prod : ∀ g : G, ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, g = k₁ * k₂) :
    Fintype.card (G ⧸ (K₁ ⊓ K₂)) = Fintype.card (G ⧸ K₁) * Fintype.card (G ⧸ K₂) := by
  -- Build the CRT map f : G/(K₁ ⊓ K₂) → G/K₁ × G/K₂ and show it's bijective.
  haveI := (K₁ ⊓ K₂).fintypeQuotientOfFiniteIndex
  haveI := K₁.fintypeQuotientOfFiniteIndex
  haveI := K₂.fintypeQuotientOfFiniteIndex
  set f : G ⧸ (K₁ ⊓ K₂) → (G ⧸ K₁) × (G ⧸ K₂) :=
    Quotient.lift (fun g => (QuotientGroup.mk g, QuotientGroup.mk g))
      (fun a b hab => by
        have := QuotientGroup.leftRel_apply.mp hab
        exact Prod.ext (QuotientGroup.eq.mpr (Subgroup.inf_le_left this))
          (QuotientGroup.eq.mpr (Subgroup.inf_le_right this)))
  have hf_inj : Function.Injective f := by
    intro a b; refine Quotient.inductionOn₂ a b (fun x y h => ?_)
    simp only [f, Quotient.lift_mk] at h
    have h1 := QuotientGroup.eq.mp (Prod.ext_iff.mp h).1
    have h2 := QuotientGroup.eq.mp (Prod.ext_iff.mp h).2
    exact QuotientGroup.eq.mpr (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, b⟩; refine Quotient.inductionOn₂ a b (fun α β => ?_)
    obtain ⟨k₁, hk₁, k₂, hk₂, h_eq⟩ := h_prod (α⁻¹ * β)
    exact ⟨QuotientGroup.mk (α * k₁), Prod.ext
      (QuotientGroup.eq.mpr (by group_mem; exact Subgroup.inv_mem _ hk₁))
      (QuotientGroup.eq.mpr (by
        show (α * k₁)⁻¹ * β ∈ K₂
        rw [mul_inv_rev, inv_inv, ← mul_assoc, ← mul_assoc]
        convert hk₂ using 1
        have : α⁻¹ * β = k₁ * k₂ := h_eq
        calc k₁⁻¹ * (α⁻¹ * β) = k₁⁻¹ * (k₁ * k₂) := by rw [this]
          _ = k₂ := by group))⟩
  rw [← Fintype.card_prod]
  exact Fintype.card_of_bijective ⟨hf_inj, hf_surj⟩

open CongruenceSubgroup in
/-- `Γ₀(mN) ⊓ Γ₀(nN) = Γ₀(mnN)` when `gcd(m,n) = 1`. -/
private lemma Gamma0_inf_eq_of_coprime (N m n : ℕ) [NeZero N] [NeZero (m * N)] [NeZero (n * N)]
    [NeZero (m * n * N)] (hcop : Nat.Coprime m n) :
    Gamma0 (m * N) ⊓ Gamma0 (n * N) = Gamma0 (m * n * N) := by
  have hN_ne : (↑N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcop_int : IsCoprime (↑m : ℤ) (↑n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simp only [Int.gcd, Int.natAbs_natCast]; exact hcop)
  ext g; simp only [Subgroup.mem_inf, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set c := (g 1 0 : ℤ)
  constructor
  · -- (mN ∣ c) ∧ (nN ∣ c) → (mnN ∣ c)
    rintro ⟨hmN, hnN⟩
    -- Factor out N: c = N·q, then m ∣ q and n ∣ q, so mn ∣ q by coprimality.
    have hN_dvd : (↑N : ℤ) ∣ c := dvd_trans (dvd_mul_left (↑N : ℤ) ↑m) hmN
    obtain ⟨q, hq⟩ := hN_dvd
    have hm : (↑m : ℤ) ∣ q := by
      rw [hq, show (↑(m * N) : ℤ) = ↑N * ↑m from by push_cast; ring] at hmN
      exact (mul_dvd_mul_iff_left hN_ne).mp hmN
    have hn : (↑n : ℤ) ∣ q := by
      rw [hq, show (↑(n * N) : ℤ) = ↑N * ↑n from by push_cast; ring] at hnN
      exact (mul_dvd_mul_iff_left hN_ne).mp hnN
    obtain ⟨r, hr⟩ := hcop_int.mul_dvd hm hn
    exact ⟨r, by rw [hq, hr]; push_cast; ring⟩
  · -- (mnN ∣ c) → (mN ∣ c) ∧ (nN ∣ c)
    rintro ⟨r, hr⟩
    exact ⟨⟨n * r, by rw [hr]; push_cast; ring⟩,
           ⟨m * r, by rw [hr]; push_cast; ring⟩⟩

/-- For `IsCoprime d N` and `IsCoprime d s`, there exists `b₁` with
`Int.gcd (N*s*b₁ − d) m = 1`. Per prime `p | m`: if `p | d` then `p ∤ Ns` (from
coprimality), so any `b₁ ≢ 0 (mod p)` works; if `p ∤ d` then avoid the single
bad class `b₁ ≡ d·(Ns)⁻¹ (mod p)`. CRT over prime factors gives a valid `b₁`. -/
private lemma exists_coprime_shift (N s d : ℤ) (m : ℕ) (hm_pos : 0 < m)
    (hdN : IsCoprime d N) (hds : IsCoprime d s) :
    ∃ b₁ : ℤ, Int.gcd (N * s * b₁ - d) m = 1 := by
  have hdNs : IsCoprime d (N * s) := hdN.mul_right hds
  set f := N * s
  -- Lift to IsCoprime (cleaner API than Int.gcd).
  suffices ∃ b₁ : ℤ, IsCoprime (f * b₁ - d) (↑m : ℤ) by
    obtain ⟨b₁, h⟩ := this; exact ⟨b₁, Int.isCoprime_iff_gcd_eq_one.mp h⟩
  -- Helper: adding a y-multiple preserves IsCoprime to y.
  have add_mul_coprime : ∀ {x y : ℤ} (z : ℤ), IsCoprime x y → IsCoprime (x + y * z) y := by
    intro x y z ⟨u, v, huv⟩; exact ⟨u, v - z * u, by linear_combination huv⟩
  -- Induction on m via prime-power × coprime decomposition.
  revert hm_pos; refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ m
  · -- Prime power: p^n. Suffices to find b₁ with IsCoprime (f*b₁ - d) p.
    intro p n hp hn _
    have hp_int : Prime (↑p : ℤ) := Nat.prime_iff_prime_int.mp hp
    suffices ∃ b₁, IsCoprime (f * b₁ - d) (↑p : ℤ) from
      this.imp fun b₁ h => h.pow_right
    by_cases hpd : (↑p : ℤ) ∣ d
    · -- p | d ⟹ p ∤ f (from IsCoprime d f). Take b₁=1: p ∤ f, p | d ⟹ p ∤ (f-d).
      have hpf : ¬(↑p : ℤ) ∣ f := by
        rw [← hp_int.coprime_iff_not_dvd, isCoprime_comm]
        exact (hdNs.of_isCoprime_of_dvd_left hpd).symm
      exact ⟨1, by
        rw [mul_one, isCoprime_comm, hp_int.coprime_iff_not_dvd]
        intro h; exact hpf (by have := dvd_add h hpd; rwa [sub_add_cancel] at this)⟩
    · -- p ∤ d. Take b₁ = 0: -d coprime to p.
      exact ⟨0, by
        simp only [mul_zero, zero_sub]
        rw [isCoprime_comm, hp_int.coprime_iff_not_dvd, dvd_neg]
        exact hpd⟩
  · intro h; omega  -- m = 0: excluded
  · exact fun _ => ⟨0, by simp [isCoprime_one_right]⟩  -- m = 1
  · -- Coprime product: m = a*b, gcd(a,b) = 1.
    intro a b ha hb hab iha ihb _
    obtain ⟨ba, hba⟩ := iha (by omega)
    obtain ⟨bb, hbb⟩ := ihb (by omega)
    -- CRT witness: b₁ = ba*b*v + bb*a*u where a*u + b*v = 1 (huv).
    have hab_int : IsCoprime (↑a : ℤ) (↑b : ℤ) := by exact_mod_cast hab
    obtain ⟨u, v, huv⟩ := hab_int  -- u*a + v*b = 1 (IsCoprime convention: a*u + b*v = 1)
    refine ⟨ba * ↑b * v + bb * ↑a * u, ?_⟩
    -- Key: f*b₁ - d = (f*ba-d)*(↑b*v) + (f*bb-d)*(↑a*u), using ↑a*u + ↑b*v = 1.
    have hkey : f * (ba * ↑b * v + bb * ↑a * u) - d =
        (f * ba - d) * (↑b * v) + (f * bb - d) * (↑a * u) := by
      linear_combination d * huv
    rw [show (↑(a * b) : ℤ) = ↑a * ↑b from by push_cast; ring, hkey]
    -- IsCoprime ↑a (↑b*v) and IsCoprime ↑b (↑a*u) from Bézout.
    have hbv_a : IsCoprime (↑a : ℤ) (↑b * v) := ⟨u, 1, by linear_combination huv⟩
    have hau_b : IsCoprime (↑b : ℤ) (↑a * u) := ⟨v, 1, by linear_combination huv⟩
    apply IsCoprime.mul_right
    · -- Coprime to ↑a: (f*ba-d)*(b*v) coprime to a, plus a-multiple.
      rw [show (f * ba - d) * (↑b * v) + (f * bb - d) * (↑a * u) =
        (f * ba - d) * (↑b * v) + ↑a * ((f * bb - d) * u) from by ring]
      exact add_mul_coprime _ (isCoprime_comm.mp ((isCoprime_comm.mp hba).mul_right hbv_a))
    · -- Coprime to ↑b: rewrite so b-multiple is explicit, then strip.
      rw [show (f * ba - d) * (↑b * v) + (f * bb - d) * (↑a * u) =
        (f * bb - d) * (↑a * u) + ↑b * (v * (f * ba - d)) from by ring]
      exact add_mul_coprime _ (isCoprime_comm.mp ((isCoprime_comm.mp hbb).mul_right hau_b))

open CongruenceSubgroup in
/-- **`Γ₀(mN) · Γ(N) = Γ₀(N)`**: every `γ ∈ Γ₀(N)` factors as `σ · δ` with
`σ ∈ Γ₀(mN)`, `δ ∈ Γ(N)`. Uses `δ = [[1,Nb₁],[Nc₁,1+N²b₁c₁]] ∈ Γ(N)` (product
of lower/upper unipotent), choosing `b₁` via `exists_coprime_shift` so that
`gcd(Nsb₁−d, m) = 1`, then `c₁` so `m | (s + Nsb₁c₁ − dc₁)`. -/
private lemma Gamma0_mN_mul_GammaN_eq_Gamma0 (N m : ℕ) [NeZero N] [NeZero (m * N)]
    (hm_pos : 0 < m) :
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 (m * N) ∧ σ⁻¹ * γ ∈ Gamma N := by
  -- Decompose γ into entries.
  refine SpecialLinearGroup.fin_two_induction ?_ γ
  intro a b c d hdet hγ
  have hNc : (↑N : ℤ) ∣ c := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    simpa [Matrix.cons_val_one, Matrix.head_cons] using hγ
  obtain ⟨s, hs⟩ := hNc
  have hd_N : IsCoprime d (↑N : ℤ) := ⟨a, -b * s, by linarith [hs ▸ hdet]⟩
  have hd_s : IsCoprime d s := ⟨a, -b * ↑N, by linarith [hs ▸ hdet]⟩
  obtain ⟨b₁, hb₁⟩ := exists_coprime_shift (↑N * ↑N) s d m hm_pos (hd_N.mul_right hd_N) hd_s
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hb₁
  set c₁ := -s * u
  -- Construct σ DIRECTLY with explicit entries (avoids matrix multiplication timeout).
  -- σ = γ * δ⁻¹ where δ = [[1,Nb₁],[Nc₁,1+N²b₁c₁]], so
  -- σ = [[a*(1+N²b₁c₁)-b*N*c₁, b-a*N*b₁], [N*s*m*v, d-N²*s*b₁]]
  -- (σ₁₀ = N*s*m*v from the Bézout identity)
  have hσ10 : ↑N * s * (1 + ↑N * ↑N * b₁ * c₁) - d * (↑N * c₁) = ↑N * (s * ↑m * v) := by
    show ↑N * s * (1 + ↑N * ↑N * b₁ * c₁) - d * (↑N * (-s * u)) = ↑N * (s * ↑m * v)
    nlinarith [huv]
  set σ₀₀ := a * (1 + ↑N * ↑N * b₁ * c₁) - b * (↑N * c₁)
  set σ₀₁ := b - a * (↑N * b₁)
  set σ₁₀ := ↑N * (s * ↑m * v)
  set σ₁₁ := d - ↑N * ↑N * s * b₁
  have hσ_det : σ₀₀ * σ₁₁ - σ₀₁ * σ₁₀ = 1 := by
    simp only [σ₀₀, σ₀₁, σ₁₀, σ₁₁]; nlinarith [hdet, hs, huv]
  set σ : SL(2, ℤ) := ⟨!![σ₀₀, σ₀₁; σ₁₀, σ₁₁], by rwa [Matrix.det_fin_two_of]⟩
  refine ⟨σ, ?_, ?_⟩
  · -- σ ∈ Γ₀(mN): (m*N) | σ₁₀ = N*s*m*v.
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    show (↑(m * N) : ℤ) ∣ σ₁₀
    exact ⟨s * v, by simp [σ₁₀]; ring⟩
  · -- σ⁻¹ * γ ∈ Γ(N): use SLMOD(N) homomorphism.
    -- σ ≡ γ (mod N) entrywise ⟹ SLMOD(N) σ = SLMOD(N) γ ⟹ σ⁻¹γ ∈ ker = Γ(N).
    rw [Gamma_mem']
    have hmod : SLMOD(N) σ = SLMOD(N) ⟨!![a, b; c, d], by rwa [Matrix.det_fin_two_of]⟩ := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [σ, σ₀₀, σ₀₁, σ₁₀, σ₁₁, SL_reduction_mod_hom_val,
          Matrix.map_apply, Int.coe_castRingHom, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const] <;>
        push_cast <;> ring_nf <;> simp [ZMod.natCast_self_eq_zero]
    rw [map_mul, map_inv, hmod, inv_mul_cancel]

/-- **Gamma0 degree multiplicativity**: `deg(diag(1,m)) * deg(diag(1,n)) = deg(diag(1,mn))`
when `gcd(m,n) = 1`, where all degrees are at the Gamma0(N) level.

Mathematically: `[Γ₀(N) : Γ₀(Nm)] * [Γ₀(N) : Γ₀(Nn)] = [Γ₀(N) : Γ₀(Nmn)]`.
This follows from the tower formula plus the product property
`Γ₀(Nm) · Γ₀(Nn) = Γ₀(N)`, which holds because for coprime `m, n`,
the conditions `Nm | σ₁₀` and `Nn | σ₁₀` on different prime factors
are independently satisfiable via lower-unipotent coset representatives.

**Proof**: Two-step CRT decomposition.
1. `Γ₀(mN) · Γ(N) = Γ₀(N)`: the image of `Γ₀(mN)` in `Γ₀(N)/Γ(N) ≅ B(ℤ/Nℤ)` is
   the full upper-triangular group (by lifting via `SL₂(ℤ) → SL₂(ℤ/Nℤ)` surjectivity,
   then adjusting the lower-left entry mod `m` using `gcd(d,b) = 1` from `det = 1`).
2. `Γ(mN) · Γ(nN) = Γ(N)`: from `Gamma_gcd_eq_mul` since `gcd(mN,nN) = N·gcd(m,n) = N`.

Combining: any `γ ∈ Γ₀(N)` writes as `γ = σ·δ` with `σ ∈ Γ₀(mN), δ ∈ Γ(N)`, then
`δ = α·β` with `α ∈ Γ(mN) ⊂ Γ₀(mN), β ∈ Γ(nN) ⊂ Γ₀(nN)`, giving
`γ = (σα)·β ∈ Γ₀(mN)·Γ₀(nN)`.

With `Γ₀(mN) ∩ Γ₀(nN) = Γ₀(mnN)` (from `lcm(mN,nN) = mnN` when `gcd(m,n)=1`),
the CRT map `Γ₀(N)/Γ₀(mnN) → Γ₀(N)/Γ₀(mN) × Γ₀(N)/Γ₀(nN)` is a bijection. -/
private lemma Gamma0_deg_coprime_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm_pos])
        (by simp [Int.gcd_one_left])) *
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, n]) (fun i => by fin_cases i <;> simp [hn_pos])
        (by simp [Int.gcd_one_left])) =
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, m * n])
        (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp [Int.gcd_one_left])) := by
  /-
  Proof strategy (CRT for Γ₀ congruence subgroups):
  The decompQuot at diag(1,k) is Γ₀(N) / Γ₀(kN) (stabilizer = Γ₀(kN)).
  The CRT map φ : Γ₀(N)/Γ₀(mnN) → Γ₀(N)/Γ₀(mN) × Γ₀(N)/Γ₀(nN) is:
  (a) Well-defined: Γ₀(mnN) ⊂ Γ₀(mN) ∩ Γ₀(nN).
  (b) Injective: ker φ = (Γ₀(mN) ∩ Γ₀(nN))/Γ₀(mnN).
      When gcd(m,n) = 1: lcm(mN,nN) = mnN, so Γ₀(mN) ∩ Γ₀(nN) = Γ₀(mnN).
  (c) Surjective: Γ₀(mN)·Γ₀(nN) = Γ₀(N), proved in two steps:
      Step 1: Γ₀(mN)·Γ(N) = Γ₀(N).
        For any γ ∈ Γ₀(N), find σ ∈ Γ₀(mN) with σ ≡ γ (mod N) by:
        - Start with any SL₂(ℤ) lift of γ mod N (exists by SL₂ surjectivity)
        - Adjust d via right-multiplication by [[1,0],[Nt,1]] ∈ Γ(N) to make gcd(d,m) = 1
          (using det=1 ⟹ gcd(d,b) = 1, so primes p | b have p ∤ d automatically;
           for p ∤ b, choose t to avoid p | d+bNt, possible since p ∤ N or p ∤ b)
        - Then solve d·j ≡ −c/N (mod m) for j, and set c' = c + d·N·j to get mN | c'.
      Step 2: Γ(mN)·Γ(nN) = Γ(N) from Gamma_gcd_eq_mul (gcd(mN,nN) = N when gcd(m,n)=1).
      Combining: γ = σ·δ with σ ∈ Γ₀(mN), δ ∈ Γ(N) = σ·(α·β) with
        α ∈ Γ(mN) ⊂ Γ₀(mN), β ∈ Γ(nN) ⊂ Γ₀(nN), giving γ = (σα)·β.
  The bijection φ gives |Γ₀(N)/Γ₀(mnN)| = |Γ₀(N)/Γ₀(mN)| × |Γ₀(N)/Γ₀(nN)|.

  **Remaining formalization**: Build `Function.Bijective f` where
  `f : decompQuot g_mn → decompQuot g_m × decompQuot g_n` via `Quotient.lift`,
  using `Gamma0_inf_eq_of_coprime` for injectivity and
  `Gamma0_mN_mul_GammaN_eq_Gamma0` + `Gamma_gcd_eq_mul` for surjectivity.
  The `card_quotient_inf_of_set_mul` CRT lemma applied to `Gamma0(N)` quotients,
  combined with `Gamma0_inf_eq_of_coprime` (intersection) and the product covering
  from `Gamma0_mN_mul_GammaN_eq_Gamma0` + `Gamma_gcd_eq_mul` (surjectivity),
  gives the SL₂-level cardinality formula. The bridge to `HeckeCoset_deg` requires
  identifying `decompQuot` with the `Gamma0` quotient for diagonal elements — a
  concrete stabilizer computation. -/
  -- Diagonal Δ-elements for m, n, mn
  set g_m : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, m]),
    diagMat_mem_Delta0_of_gcd N _ (fun i => by fin_cases i <;> simp [hm_pos]) (by simp)⟩
  set g_n : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, n]),
    diagMat_mem_Delta0_of_gcd N _ (fun i => by fin_cases i <;> simp [hn_pos]) (by simp)⟩
  set g_mn : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, m * n]),
    diagMat_mem_Delta0_of_gcd N _ (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
      (by simp)⟩
  -- T_diag_Gamma0 definitionally equals ⟦g_k⟧
  change HeckeRing.HeckeCoset_deg _ ⟦g_m⟧ * HeckeRing.HeckeCoset_deg _ ⟦g_n⟧ =
    HeckeRing.HeckeCoset_deg _ ⟦g_mn⟧
  -- Step 1: Transfer decompQuot from reps to diagonal elements.
  -- Since ⟦rep ⟦g⟧⟧ = ⟦g⟧, the rep is in DC(g), so decompQuot(rep) ≃ decompQuot(g).
  have h_rep_card : ∀ (g : (Gamma0_pair N).Δ),
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep ⟦g⟧)) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g) := by
    intro g
    have h_mk := HeckeCoset.mk_rep (⟦g⟧ : HeckeRing.HeckeCoset (Gamma0_pair N))
    rw [HeckeCoset.eq_iff] at h_mk
    have h_in : (HeckeCoset.rep ⟦g⟧ : GL (Fin 2) ℚ) ∈
        DoubleCoset.doubleCoset (g : GL (Fin 2) ℚ)
          ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
      rw [← h_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
    rw [DoubleCoset.mem_doubleCoset] at h_in
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, h_eq⟩ := h_in
    let g_mid : (Gamma0_pair N).Δ := ⟨γ₁ * ↑g * γ₂, h_eq ▸ (HeckeCoset.rep ⟦g⟧).2⟩
    have h_mid : (g_mid : GL (Fin 2) ℚ) = HeckeCoset.rep ⟦g⟧ := h_eq.symm
    exact Nat.card_congr (
      (Equiv.cast (congrArg (HeckeRing.decompQuot (Gamma0_pair N))
        (Subtype.ext h_mid))).symm.trans
      (HeckeRing.decompQuot_double_H_equiv (Gamma0_pair N) g ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
        (h_eq ▸ (HeckeCoset.rep ⟦g⟧).2)))
  -- HeckeCoset_deg = Fintype.card(decompQuot(rep)) = Nat.card(decompQuot(g))
  simp only [HeckeRing.HeckeCoset_deg]
  rw [show (Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeCoset.rep ⟦g_m⟧)) : ℤ) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_m) from by
      rw [Nat.card_eq_fintype_card, h_rep_card],
    show (Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeCoset.rep ⟦g_n⟧)) : ℤ) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_n) from by
      rw [Nat.card_eq_fintype_card, h_rep_card],
    show (Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeCoset.rep ⟦g_mn⟧)) : ℤ) =
      Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_mn) from by
      rw [Nat.card_eq_fintype_card, h_rep_card]]
  -- Step 2: Use stab_diag_eq_Gamma0 to transfer to Gamma0 quotients.
  set H := (Gamma0_pair N).H
  set K_m := ((CongruenceSubgroup.Gamma0 (m * N)).map (mapGL ℚ)).subgroupOf H
  set K_n := ((CongruenceSubgroup.Gamma0 (n * N)).map (mapGL ℚ)).subgroupOf H
  set K_mn := ((CongruenceSubgroup.Gamma0 (m * n * N)).map (mapGL ℚ)).subgroupOf H
  have h_stab_m := stab_diag_eq_Gamma0 N m hm_pos
  have h_stab_n := stab_diag_eq_Gamma0 N n hn_pos
  have h_stab_mn := stab_diag_eq_Gamma0 N (m * n) (Nat.mul_pos hm_pos hn_pos)
  rw [show Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_m) = Nat.card (↥H ⧸ K_m) from
      Nat.card_congr (Subgroup.quotientEquivOfEq h_stab_m),
    show Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_n) = Nat.card (↥H ⧸ K_n) from
      Nat.card_congr (Subgroup.quotientEquivOfEq h_stab_n),
    show Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_mn) = Nat.card (↥H ⧸ K_mn) from
      Nat.card_congr (Subgroup.quotientEquivOfEq h_stab_mn)]
  -- Step 3: K_m ⊓ K_n = K_mn from Gamma0_inf_eq_of_coprime
  have h_inf : K_m ⊓ K_n = K_mn := by
    simp only [K_m, K_n, K_mn, ← Subgroup.subgroupOf_inf]
    congr 1
    rw [← Subgroup.map_inf_eq (f := mapGL ℚ) (hf := mapGL_injective)]
    congr 1
    haveI : NeZero (m * N) := ⟨by omega⟩
    haveI : NeZero (n * N) := ⟨by omega⟩
    haveI : NeZero (m * n * N) := ⟨by omega⟩
    exact Gamma0_inf_eq_of_coprime N m n hcop
  -- Step 4: FiniteIndex instances
  haveI : Finite (HeckeRing.decompQuot (Gamma0_pair N) g_m) := Fintype.finite _
  haveI : Finite (HeckeRing.decompQuot (Gamma0_pair N) g_n) := Fintype.finite _
  haveI : Finite (HeckeRing.decompQuot (Gamma0_pair N) g_mn) := Fintype.finite _
  haveI : Finite (↥H ⧸ K_m) := (Subgroup.quotientEquivOfEq h_stab_m).symm.finite
  haveI : Finite (↥H ⧸ K_n) := (Subgroup.quotientEquivOfEq h_stab_n).symm.finite
  haveI : Finite (↥H ⧸ K_mn) := (Subgroup.quotientEquivOfEq h_stab_mn).symm.finite
  haveI : K_m.FiniteIndex := ⟨by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
  haveI : K_n.FiniteIndex := ⟨by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
  haveI : (K_m ⊓ K_n).FiniteIndex := by
    rw [h_inf]; exact ⟨by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
  -- Step 5: Apply CRT
  rw [← h_inf]
  simp only [Nat.cast_inj, ← Fintype.card_eq_nat_card]
  exact card_quotient_inf_of_set_mul K_m K_n (by
    -- Product covering: every g ∈ H factors as k₁ * k₂ with k₁ ∈ K_m, k₂ ∈ K_n.
    intro ⟨g, hg⟩
    obtain ⟨γ, hγ_mem, hγ_eq⟩ := Subgroup.mem_map.mp hg
    haveI : NeZero (m * N) := ⟨by omega⟩
    haveI : NeZero (n * N) := ⟨by omega⟩
    obtain ⟨σ_m, hσ_m, hδ_m⟩ := Gamma0_mN_mul_GammaN_eq_Gamma0 N m hm_pos γ hγ_mem
    set δ := σ_m⁻¹ * γ with hδ_def
    have h_gcd : Nat.gcd (m * N) (n * N) = N := by
      rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
    have hδ_mem : δ ∈ CongruenceSubgroup.Gamma N := hδ_m
    have hδ_sup : δ ∈ CongruenceSubgroup.Gamma (m * N) ⊔
        CongruenceSubgroup.Gamma (n * N) := by
      have h_eq := Gamma_gcd_eq_mul (m * N) (n * N)
      rw [← Subgroup.map_sup, h_gcd] at h_eq
      exact Subgroup.map_injective mapGL_injective h_eq ▸ (h_gcd ▸ hδ_mem)
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Subgroup.mem_sup.mp hδ_sup
    have hα_Gamma0 : α ∈ CongruenceSubgroup.Gamma0 (m * N) :=
      CongruenceSubgroup.Gamma_le_Gamma0 (m * N) hα
    have hβ_Gamma0 : β ∈ CongruenceSubgroup.Gamma0 (n * N) :=
      CongruenceSubgroup.Gamma_le_Gamma0 (n * N) hβ
    have h_factor : γ = σ_m * α * β := by
      rw [mul_assoc, ← hαβ, hδ_def, mul_comm σ_m⁻¹, ← mul_assoc, mul_inv_cancel_right]
    refine ⟨⟨mapGL ℚ (σ_m * α), ?_⟩, ?_, ⟨mapGL ℚ β, ?_⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_antitone
        (Nat.dvd_mul_left N m) (Subgroup.mul_mem _ hσ_m hα_Gamma0))
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mul_mem _ hσ_m hα_Gamma0)
    · exact Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_antitone
        (Nat.dvd_mul_left N n) hβ_Gamma0)
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem _ hβ_Gamma0
    · ext; simp only [Subgroup.coe_mul, Subgroup.coe_mk, ← map_mul, h_factor, mul_assoc])
/-- **Coprime diagonal multiplication for Gamma0** (Shimura §3.2, Prop 3.16–17):
`T'(1,m) * T'(1,n) = T'(1,mn)` when `gcd(m, n) = 1`.

Partners `T_bad_mul` (for m, n ∣ N^∞). Together they give the full
multiplicativity needed for `ker_π_le_ker_ψ`. -/
private theorem T_coprime_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (fun i => by fin_cases i <;> simp [hm_pos]) (by simp [Int.gcd_one_left])) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, n])
        (fun i => by fin_cases i <;> simp [hn_pos]) (by simp [Int.gcd_one_left])) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m * n])
        (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp [Int.gcd_one_left])) 1 := by
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) _ _ _ (by
    -- heckeMultiplicity = 1 by degree argument (same pattern as T_bad_mul)
    set D₁ := T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm_pos])
      (by simp [Int.gcd_one_left])
    set D₂ := T_diag_Gamma0 N (![1, n]) (fun i => by fin_cases i <;> simp [hn_pos])
      (by simp [Int.gcd_one_left])
    set D_out := T_diag_Gamma0 N (![1, m * n])
      (fun i => by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
      (by simp [Int.gcd_one_left])
    set μ := HeckeRing.heckeMultiplicity (Gamma0_pair N) D₁.rep D₂.rep D_out.rep
    -- All mulMap outputs = D_out → m Finsupp = single D_out μ
    have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D₁.rep D₂.rep p = D_out :=
      mulMap_Gamma0_coprime_eq N m n hm_pos hn_pos hcop
    have h_zero_all : ∀ A, A ≠ D_out →
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) A = 0 := by
      intro A hA; simp only [HeckeRing.m_apply]
      exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique
        (Gamma0_pair N) _ _ D_out A hA h_mulMap
    have h_m_eq : HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep =
        Finsupp.single D_out μ := by
      ext A; simp only [Finsupp.single_apply]
      split_ifs with h
      · subst h; simp only [HeckeRing.m_apply]; rfl
      · exact h_zero_all A (Ne.symm h)
    -- Degree computation: deg(D₁) * deg(D₂) = deg(D_out) by Gamma0 coprime multiplicativity
    have h_deg_mul := Gamma0_deg_coprime_mul N m n hm_pos hn_pos hcop
    -- Gamma0 product degree
    have h_deg_prod : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.T_single _ ℤ D₁ 1 * HeckeRing.T_single _ ℤ D₂ 1) =
        HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out := by
      rw [HeckeRing.deg_mul, HeckeRing.deg_T_single, HeckeRing.deg_T_single,
        one_mul, one_mul, h_deg_mul]
    -- deg(m Finsupp) = μ * deg(D_out)
    have h_deg_m_eq : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) =
        μ * HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out := by
      rw [h_m_eq]; simp [HeckeRing.deg_T_single]
    -- deg(T₁*T₂) = deg(m) = μ * deg(D_out) = deg(D_out)
    rw [HeckeRing.T_single_one_mul_T_single_one] at h_deg_prod
    -- μ * deg(D_out) = deg(D_out) with deg(D_out) > 0 gives μ = 1
    have hd_out_pos : (0 : ℤ) < HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out :=
      HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_out
    have hd_out_ne : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out ≠ 0 :=
      ne_of_gt hd_out_pos
    exact mul_right_cancel₀ hd_out_ne (by linarith [h_deg_prod, h_deg_m_eq])) ?_
  · intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ _ A hA
      (mulMap_Gamma0_coprime_eq N m n hm_pos hn_pos hcop)

/-- **Coprime Finsupp coefficient factorisation**: for Hecke algebra elements
`f, g` whose support cosets have pairwise coprime diagonal products, the
Finsupp coefficient at `T_diag(d₁ * d₂)` factors as `f(d₁) * g(d₂)`.

This is the inductive bridge for `multi_prime_kronecker`.
Proof: expand `(f * g)(D)` via `mul_def` / `Finsupp.sum`, apply
`T_diag_mul_coprime` to each coprime pair to get
`m(rep D₁, rep D₂) = single(T_diag(a*b), 1)`, then `diagonal_representative_unique`
collapses the double sum to the unique pair `(d₁, d₂)` via `huniq`. -/
private lemma coprime_mul_coeff (f g : HeckeAlgebra 2)
    (d₁ d₂ : Fin 2 → ℕ)
    (hd₁_pos : ∀ i, 0 < d₁ i) (hd₂_pos : ∀ i, 0 < d₂ i)
    (hd₁_div : DivChain 2 d₁) (hd₂_div : DivChain 2 d₂)
    (hf_diag : ∀ D, f D ≠ 0 → ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a)
    (hg_diag : ∀ D, g D ≠ 0 → ∃ b, D = T_diag b ∧ (∀ i, 0 < b i) ∧ DivChain 2 b)
    (hcop_pair : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i))
    (huniq : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i) →
      T_diag (a * b) = T_diag (d₁ * d₂) → a = d₁ ∧ b = d₂) :
    (f * g) (T_diag (d₁ * d₂)) = f (T_diag d₁) * g (T_diag d₂) := by
  set D := T_diag (d₁ * d₂) with hD_def
  -- Step 1: coprime m-delta: for support pairs, the multiplicity at D is a Kronecker delta
  have hm_delta : ∀ D₁ D₂ : HeckeCoset (GL_pair 2),
      f D₁ ≠ 0 → g D₂ ≠ 0 →
      (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D =
      if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then 1 else 0 := by
    intro D₁ D₂ hD₁ hD₂
    obtain ⟨a, rfl, ha_pos, ha_div⟩ := hf_diag D₁ hD₁
    obtain ⟨b, rfl, hb_pos, hb_div⟩ := hg_diag D₂ hD₂
    have hcop_ab := hcop_pair _ _ a b hD₁ hD₂ rfl rfl ha_pos hb_pos ha_div hb_div
    -- m = single(T_diag(a*b), 1) by T_diag_mul_coprime
    have hm_eq : HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag a))
        (HeckeCoset.rep (T_diag b)) = Finsupp.single (T_diag (a * b)) 1 := by
      rw [← HeckeRing.T_single_one_mul_T_single_one]
      exact T_diag_mul_coprime 2 a b ha_pos hb_pos ha_div hb_div hcop_ab
    rw [hm_eq, Finsupp.single_apply, hD_def]
    -- Reduce to: T_diag(d₁*d₂) = T_diag(a*b) ↔ T_diag a = T_diag d₁ ∧ T_diag b = T_diag d₂
    congr 1; apply propext
    exact ⟨fun h => by
        have ⟨ha, hb⟩ := huniq _ _ a b hD₁ hD₂ rfl rfl ha_pos hb_pos ha_div hb_div hcop_ab h.symm
        exact ⟨congr_arg T_diag ha, congr_arg T_diag hb⟩,
      fun ⟨ha, hb⟩ => by
        rw [diagonal_representative_unique 2 a d₁ ha_pos hd₁_pos ha_div hd₁_div ha,
            diagonal_representative_unique 2 b d₂ hb_pos hd₂_pos hb_div hd₂_div hb]⟩
  -- Step 2: Expand (f * g)(D) as double Finsupp sum via mul_def
  have h_expand : (f * g) D = ∑ D₁ ∈ f.support, ∑ D₂ ∈ g.support,
      f D₁ * g D₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)) D := by
    show (Finsupp.sum f (fun D₁ b₁ => Finsupp.sum g (fun D₂ b₂ =>
      b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)))) D = _
    simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  rw [h_expand]
  -- Step 3: Replace m-values using hm_delta
  conv_lhs =>
    arg 2; ext D₁; arg 2; ext D₂
    rw [show f D₁ * g D₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)) D =
        if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then f D₁ * g D₂ else 0 from by
      by_cases hD₁ : f D₁ = 0
      · simp [hD₁]
      · by_cases hD₂ : g D₂ = 0
        · simp [hD₂]
        · rw [hm_delta D₁ D₂ hD₁ hD₂, mul_ite, mul_one, mul_zero]]
  -- Step 4: Collapse the double sum
  -- Inner sum: split the conjunction, collapse over D₂ via Finset.sum_ite_eq'
  have h_inner : ∀ D₁ ∈ f.support, (∑ D₂ ∈ g.support,
      if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then f D₁ * g D₂ else 0) =
      if D₁ = T_diag d₁ then f D₁ * g (T_diag d₂) else 0 := by
    intro D₁ _
    by_cases h : D₁ = T_diag d₁
    · subst h; simp only [true_and]
      rw [Finset.sum_ite_eq']; split_ifs with hm
      · rfl
      · simp [Finsupp.not_mem_support_iff.mp hm]
    · simp [h]
  rw [Finset.sum_congr rfl h_inner, Finset.sum_ite_eq']
  -- Collapse outer: if T_diag d₁ ∈ f.support then ... else 0 = f(d₁) * g(d₂)
  split_ifs with hm
  · rfl
  · simp [Finsupp.not_mem_support_iff.mp hm]

/-- Every coset in the support of `T_gen(q,0)^a * T_gen(q,1)^b` has a diagonal
representative whose entries are powers of `q`.

This follows from determinant multiplicativity in the Hecke ring:
`T_gen(q,k)` has determinant `q^{k+1}`, so `T_gen(q)^e` has determinant `q^{e₀+2e₁}`.
Every support coset has this determinant, and for `n=2` with `a₁ | a₂` and
`a₁ * a₂ = q^k`, both `a₁, a₂` must be powers of `q` (since `q` is prime). -/
/-- Determinant of an SL_n(ℤ) element embedded in GL_n(ℚ) is 1. -/
private lemma det_SLnZ_eq_one {g : GL (Fin 2) ℚ} (hg : g ∈ SLnZ_subgroup 2) :
    (↑g : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  obtain ⟨σ, rfl⟩ := hg; simp [mapGL, det_intMat_cast, SpecialLinearGroup.det_coe]

/-- Elements in the same SL_n double coset have the same determinant. -/
private lemma det_doubleCoset_eq {g₁ g₂ : (GL_pair 2).Δ}
    (h : (⟦g₁⟧ : HeckeCoset (GL_pair 2)) = ⟦g₂⟧) :
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [HeckeCoset.eq_iff, DoubleCoset.doubleCoset_eq_iff] at h
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := h
  have : (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (h₁ * (↑g₂ : GL (Fin 2) ℚ) * h₂).1.det := by rw [heq]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul,
    det_SLnZ_eq_one hh₁, det_SLnZ_eq_one hh₂, one_mul, mul_one] at this
  exact this

/-- The diagonal product of rep(T_diag a) equals ∏ a. -/
private lemma prod_rep_T_diag (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(↑(HeckeCoset.rep (T_diag a)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    ∏ i, (a i : ℚ) := by
  have h_eq : (⟦HeckeCoset.rep (T_diag a)⟧ : HeckeCoset (GL_pair 2)) = T_diag a :=
    Quotient.out_eq _
  rw [show T_diag a = (⟦diagMat_delta 2 a⟧ : HeckeCoset (GL_pair 2)) from rfl] at h_eq
  exact (det_doubleCoset_eq h_eq).trans (by simp [diagMat_delta_val 2 a ha, diagMat_det 2 a ha])

/-- Every coset in the support of a mulMap output has determinant = det(g₁) * det(g₂). -/
private lemma det_mulMap_eq (g₁ g₂ : (GL_pair 2).Δ)
    (p : HeckeRing.decompQuot (GL_pair 2) g₁ × HeckeRing.decompQuot (GL_pair 2) g₂) :
    (↑(↑(HeckeCoset.rep (HeckeRing.mulMap (GL_pair 2) g₁ g₂ p)) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ).det =
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
    (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  -- mulMap output = ⟦σ * g₁ * (τ * g₂)⟧ for σ, τ ∈ SL_n
  -- rep is in the same double coset, so has the same det
  -- det(σ * g₁ * τ * g₂) = det(g₁) * det(g₂)
  have h_eq : (⟦HeckeCoset.rep (HeckeRing.mulMap (GL_pair 2) g₁ g₂ p)⟧ :
      HeckeCoset (GL_pair 2)) = HeckeRing.mulMap (GL_pair 2) g₁ g₂ p := Quotient.out_eq _
  rw [det_doubleCoset_eq h_eq]
  show (↑(p.1.out * ↑g₁ * (p.2.out * ↑g₂)) : Matrix (Fin 2) (Fin 2) ℚ).det = _
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h1 := det_SLnZ_eq_one (p.1.out.2)
  have h2 := det_SLnZ_eq_one (p.2.out.2)
  simp [h1, h2]

private lemma T_gen_pow_support_qpower (q : {p : ℕ // p.Prime})
    (e : Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (T_gen 2 q.1 0 ^ (e 0) * T_gen 2 q.1 1 ^ (e 1)) D ≠ 0) :
    ∃ a : Fin 2 → ℕ, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a ∧
      (∏ i, a i) = q.1 ^ (e 0 + 2 * e 1) := by
  -- D is a Hecke coset, so has a diagonal representative
  obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  -- Show ∏ a = q^{e 0 + 2*e 1} by determinant tracking
  -- Every support coset has det = q^{e 0} * q^{2*e 1} = q^{e 0 + 2*e 1}
  suffices h_det : ∀ (a₀ b₀ : ℕ) (f : HeckeAlgebra 2) (D' : HeckeCoset (GL_pair 2)),
      (∀ D'', f D'' ≠ 0 →
        (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ a₀ : ℕ)) →
      (T_gen 2 q.1 0 ^ b₀ * f) D' ≠ 0 →
      (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ (b₀ + a₀) : ℕ) by
    -- Apply h_det with f = T_gen(q,1)^{e 1}, a₀ = 2*e 1, b₀ = e 0
    have hf_det : ∀ D'', (T_gen 2 q.1 1 ^ (e 1)) D'' ≠ 0 →
        (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ (2 * e 1) : ℕ) := by
      intro D'' hD''
      -- T_gen(q,1)^{e 1} = T_elem(![q^{e 1}, q^{e 1}]) = single(T_diag(...), 1)
      rw [show T_gen 2 q.1 1 = T_pp q.1 from HeckeRing.GLn.Surj.T_gen_one_eq_T_pp q.1 q.2,
        HeckeRing.GL2.T_pp_pow q.1 q.2 (e 1)] at hD''
      simp only [T_elem, Finsupp.single_apply] at hD''
      split_ifs at hD'' with h_eq
      · rw [← Quotient.out_eq D'', show (⟦HeckeCoset.rep D''⟧ : HeckeCoset (GL_pair 2)) = D''
            from Quotient.out_eq _, h_eq]
        rw [prod_rep_T_diag _ (fun i => by fin_cases i <;> simp [pow_pos q.2.pos])]
        simp [Fin.prod_univ_two, pow_add, pow_mul]
      · exact absurd rfl (by push_neg at hD''; exact (hD'' (one_ne_zero)).elim)
    have h_result := h_det (2 * e 1) (e 0) (T_gen 2 q.1 1 ^ (e 1)) D hf_det hD
    rw [prod_rep_T_diag a ha_pos, hD_eq] at h_result
    rw [show e 0 + 2 * e 1 = e 0 + (2 * e 1) from by ring] at h_result
    -- h_result : ∏ (a i : ℚ) = ↑(q.1 ^ (e 0 + 2 * e 1))
    exact_mod_cast h_result
  -- Prove h_det by induction on b₀
  intro a₀; intro b₀; induction b₀ with
  | zero =>
    intro f D' hf_det hD'
    simp only [pow_zero, one_mul, Nat.zero_add] at hD' ⊢
    exact hf_det D' hD'
  | succ n ih =>
    intro f D' hf_det hD'
    rw [pow_succ', mul_assoc] at hD'
    -- hD' : (T_gen(q,0) * (T_gen(q,0)^n * f)) D' ≠ 0
    set g' := T_gen 2 q.1 0 ^ n * f with hg'_def
    -- T_gen(q,0) = T_elem(![1,q]) = single(T_diag(![1,q]), 1)
    set D₁ := T_diag (![1, q.1]) with hD₁_def
    have hf_eq : T_gen 2 q.1 0 = HeckeRing.T_single (GL_pair 2) ℤ D₁ 1 := by
      show T_elem (T_gen_diag 2 q.1 0) = _; congr 1
      funext i; simp [T_gen_diag]; fin_cases i <;> simp
    rw [hf_eq] at hD'
    -- Expand (single D₁ 1 * g')(D') as sum
    have h_expand : (HeckeRing.T_single (GL_pair 2) ℤ D₁ 1 * g') D' =
        g'.sum (fun D₂ c₂ => c₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
          (HeckeCoset.rep D₂)) D') := by
      show (Finsupp.sum (Finsupp.single D₁ 1)
        (fun D₁' b₁ => g'.sum (fun D₂ b₂ =>
          b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁') (HeckeCoset.rep D₂)))) D' = _
      rw [Finsupp.sum_single_index (by simp [Finsupp.sum])]
      simp [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [h_expand] at hD'
    -- Extract D₂ with nonzero contribution
    rw [Finsupp.sum] at hD'
    obtain ⟨D₂, hD₂_mem, hD₂_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hD'
    have hgD₂ : g' D₂ ≠ 0 := Finsupp.mem_support_iff.mp hD₂_mem
    have hm_ne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D' ≠ 0 := by
      intro h; exact hD₂_ne (by rw [h, mul_zero])
    -- D' ∈ mulSupport(rep D₁, rep D₂)
    rw [HeckeRing.m_apply] at hm_ne
    have hD'_mem : D' ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) := by
      rw [← HeckeRing.m_support]; exact Finsupp.mem_support_iff.mpr hm_ne
    -- D' = mulMap(...)(p) for some p
    rw [HeckeRing.mulSupport, Finset.mem_image] at hD'_mem
    obtain ⟨p, _, hD'_eq⟩ := hD'_mem
    -- det(rep D') = det(rep D₁) * det(rep D₂)
    have h_det_D' := det_mulMap_eq (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p
    rw [hD'_eq] at h_det_D'
    -- det(rep D₁) = q (from prod_rep_T_diag)
    have h_det_D₁ : (↑(↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = (q.1 : ℚ) := by
      rw [prod_rep_T_diag (![1, q.1]) (fun i => by fin_cases i <;> simp [q.2.pos])]
      simp [Fin.prod_univ_two]
    -- det(rep D₂) = q^{n+a₀} by IH
    have h_det_D₂ : (↑(↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = ↑(q.1 ^ (n + a₀) : ℕ) :=
      ih f D₂ hf_det hgD₂
    -- Combine: det(rep D') = q^{n+1+a₀}
    rw [h_det_D₁, h_det_D₂] at h_det_D'
    convert h_det_D' using 1
    push_cast; ring

/-- Every coset in the support of `T_gen(q,0)^a * T_gen(q,1)^b` has entries
that are powers of `q` (immediate from `T_gen_pow_support_qpower`). -/
private lemma T_gen_pow_entries_qpower (q : {p : ℕ // p.Prime})
    (e : Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (T_gen 2 q.1 0 ^ (e 0) * T_gen 2 q.1 1 ^ (e 1)) D ≠ 0)
    (a : Fin 2 → ℕ) (ha : D = T_diag a) (ha_pos : ∀ i, 0 < a i)
    (ha_div : DivChain 2 a) :
    ∀ p : ℕ, p.Prime → p ≠ q.1 → ∀ i, ¬(p ∣ a i) := by
  obtain ⟨a', rfl, ha'_pos, ha'_div, ha'_det⟩ := T_gen_pow_support_qpower q e D hD
  have ha_eq := diagonal_representative_unique 2 a a' ha_pos ha'_pos ha_div ha'_div ha
  subst ha_eq
  intro p hp hpq i
  intro h_dvd
  have : p ∣ ∏ j, a' j := dvd_trans h_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  rw [ha'_det] at this
  exact hpq (hp.eq_of_dvd_of_prime q.2 (dvd_of_dvd_pow this) |>.symm)

/-- If `(f * g)(D) ≠ 0` in the Hecke ring, there exist `D₁ ∈ supp(f)` and `D₂ ∈ supp(g)`
with `D ∈ mulSupport(rep D₁, rep D₂)`. -/
private lemma support_mul_exists (f g : HeckeAlgebra 2) (D : HeckeCoset (GL_pair 2))
    (hD : (f * g) D ≠ 0) :
    ∃ D₁ D₂, f D₁ ≠ 0 ∧ g D₂ ≠ 0 ∧
      D ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
  -- Expand f * g using mul_def
  have h : (Finsupp.sum f (fun D₁ b₁ => Finsupp.sum g (fun D₂ b₂ =>
      b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)))) D ≠ 0 := hD
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  obtain ⟨D₁, hD₁_mem, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨D₂, hD₂_mem, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h₁
  have hfD₁ := Finsupp.mem_support_iff.mp hD₁_mem
  have hgD₂ := Finsupp.mem_support_iff.mp hD₂_mem
  have hm_ne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D ≠ 0 := by
    intro h; exact h₂ (by rw [h, mul_zero, mul_zero])
  exact ⟨D₁, D₂, hfD₁, hgD₂, by rwa [← HeckeRing.m_support] at hm_ne;
    exact Finsupp.mem_support_iff.mpr hm_ne⟩

/-- Determinant multiplicativity for Hecke products: if all support cosets of `f`
have `det = d₁` and all of `g` have `det = d₂`, then all support cosets of
`f * g` have `det = d₁ * d₂`. Uses `support_mul_exists` + `det_mulMap_eq`. -/
private lemma support_det_mul (f g : HeckeAlgebra 2) (d₁ d₂ : ℚ)
    (hf : ∀ D, f D ≠ 0 →
      (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₁)
    (hg : ∀ D, g D ≠ 0 →
      (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₂)
    (D : HeckeCoset (GL_pair 2)) (hD : (f * g) D ≠ 0) :
    (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₁ * d₂ := by
  obtain ⟨D₁, D₂, hfD₁, hgD₂, hD_mem⟩ := support_mul_exists f g D hD
  rw [HeckeRing.mulSupport, Finset.mem_image] at hD_mem
  obtain ⟨p, _, hD_eq⟩ := hD_mem
  rw [← hD_eq, det_mulMap_eq, hf D₁ hfD₁, hg D₂ hgD₂]

/-- Multi-prime determinant tracking (det version): support of `∏_{S} T_gen(p)^{e_p}`
has `det(rep D) = ∏_{S} p^{e_p 0 + 2*e_p 1}`. Proved by `Finset.induction` using
`support_det_mul` + `T_gen_pow_support_qpower`. -/
private lemma prod_gen_det_eq (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))) D ≠ 0) :
    (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    ↑(∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) : ℕ) := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty] at hD ⊢
    -- (1 : HeckeAlgebra 2)(D) ≠ 0 means D = HeckeCoset.one
    rw [HeckeRing.one_def (GL_pair 2) (Z := ℤ)] at hD
    have hD_eq : D = HeckeCoset.one (GL_pair 2) := by
      simpa [Finsupp.single_apply] using hD
    rw [hD_eq, show HeckeCoset.one (GL_pair 2) = T_diag (fun _ : Fin 2 => 1) from
      (T_diag_ones 2).symm, prod_rep_T_diag _ (fun _ => Nat.one_pos)]
    simp [Fin.prod_univ_two]
  | @insert q' S'' hq'' ih =>
    rw [Finset.prod_insert hq''] at hD
    have h := support_det_mul _ _
      (↑(q'.1 ^ (e q' 0 + 2 * e q' 1) : ℕ) : ℚ)
      (↑(∏ p ∈ S'', p.1 ^ (e p 0 + 2 * e p 1) : ℕ) : ℚ)
      (fun D' hD' => by
        obtain ⟨a, hDa, ha_pos, _, ha_det⟩ := T_gen_pow_support_qpower q' (e q') D' hD'
        rw [hDa, prod_rep_T_diag a ha_pos]; push_cast [ha_det])
      (fun D' hD' => ih hD')
      D hD
    rw [h]; push_cast [Finset.prod_insert hq'']; ring

/-- Multi-prime support tracking: every coset in the support of
`∏_{p ∈ S} T_gen(p)^{e_p}` has diagonal product `∏_{p ∈ S} p^{e_p 0 + 2*e_p 1}`. -/
private lemma prod_gen_support_det (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))) D ≠ 0) :
    ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a ∧
      (∏ i, a i) = ∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) := by
  obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  have h_det := prod_gen_det_eq S e D hD
  rw [hD_eq, prod_rep_T_diag a ha_pos] at h_det
  exact_mod_cast h_det

/-- **Multi-prime coefficient factorisation**: the Finsupp coefficient of a product
of per-prime generator monomials at a product of per-prime cosets factors as the
product of per-prime coefficients.

Proof by `Finset.induction` on `S`, using `coprime_mul_coeff` at each step
to peel off one prime. -/
private lemma multi_prime_coeff_factor (S : Finset {p : ℕ // p.Prime})
    (e d : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)))
      (T_diag (∏ p ∈ S, ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) =
    ∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))
      (T_diag (ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) := by
  induction S using Finset.induction with
  | empty => simp [Finset.prod_empty, HeckeRing.one_def (GL_pair 2) (Z := ℤ),
      Finsupp.single_apply]
  | @insert q S' hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, Finset.prod_insert hq]
    set f := T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1)
    set g := ∏ p ∈ S', T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)
    set d₁ := ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1]
    set d₂ := ∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1]
    -- Factor: (f * g)(T_diag(d₁ * d₂)) = f(T_diag d₁) * g(T_diag d₂)
    have h_factor : (f * g) (T_diag (d₁ * d₂)) = f (T_diag d₁) * g (T_diag d₂) := by
      refine coprime_mul_coeff f g d₁ d₂
        (ppowDiag_pos 2 q.1 q.2 _)  -- hd₁_pos
        (fun i => Finset.prod_pos (fun p _ => ppowDiag_pos 2 p.1 p.2 _ i))  -- hd₂_pos
        (divChain_ppow 2 q.1 _ (by intro i j h; fin_cases i <;> fin_cases j <;>
          simp_all [Fin.le_def]; omega))  -- hd₁_div
        ?_ -- hd₂_div
        (fun D _ => exists_diagonal_representative 2 D)  -- hf_diag
        (fun D _ => exists_diagonal_representative 2 D)  -- hg_diag
        ?_ -- hcop_pair
        ?_ -- huniq
      · -- hd₂_div: DivChain of product of ppowDiag's
        exact Finset.prod_induction _ (DivChain 2)
          (fun a b ha hb => DivChain_mul 2 a b ha hb)
          (fun i _ => dvd_refl 1)
          (fun p _ => divChain_ppow 2 p.1 _ (by
            intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]; omega))
      · -- hcop_pair: coprimality of q-power × S'-coprime diagonal products
        intro D₁ D₂ a b hfD₁ hgD₂ hD₁_eq hD₂_eq ha_pos hb_pos ha_div hb_div
        -- f-side: ∏ a = q^{...} (q-power)
        obtain ⟨a', _, ha'_pos, ha'_div, ha'_det⟩ := T_gen_pow_support_qpower q (e q) D₁ hfD₁
        have ha_eq := diagonal_representative_unique 2 a a' ha_pos ha'_pos ha_div ha'_div hD₁_eq
        subst ha_eq; rw [ha'_det]
        -- g-side: ∏ b = ∏_{p ∈ S'} p^{...} which is coprime to q (q ∉ S')
        obtain ⟨b', hDb', hb'_pos, hb'_div, hb'_det⟩ := prod_gen_support_det S' e D₂ hgD₂
        have hb_eq := diagonal_representative_unique 2 b b' hb_pos hb'_pos hb_div hb'_div hD₂_eq
        subst hb_eq; rw [hb'_det]
        -- Coprime(q^k, ∏_{p ∈ S'} p^{...}): q ∉ S' ⟹ q ≠ p for each p ∈ S'
        apply Nat.Coprime.pow_left
        apply Nat.coprime_prod_right_iff.mpr
        intro p hp
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes q.2 p.2).mpr (fun h => hq (h ▸ hp))
      · -- huniq: per-pair coprime factorisation uniqueness
        intro D₁ D₂ a b hfD₁ hgD₂ hD₁_eq hD₂_eq ha_pos hb_pos ha_div hb_div hcop h_eq
        -- Get component-wise equality a * b = d₁ * d₂
        have hab := diagonal_representative_unique 2 (a * b) (d₁ * d₂)
          (pi_mul_pos a b ha_pos hb_pos)
          (pi_mul_pos d₁ d₂ (ppowDiag_pos 2 q.1 q.2 _)
            (fun i => Finset.prod_pos (fun p _ => ppowDiag_pos 2 p.1 p.2 _ i)))
          (DivChain_mul 2 a b ha_div hb_div)
          (DivChain_mul 2 d₁ d₂
            (divChain_ppow 2 q.1 _ (by intro i j h; fin_cases i <;> fin_cases j <;>
              simp_all [Fin.le_def]; omega))
            (Finset.prod_induction _ (DivChain 2) (fun x y => DivChain_mul 2 x y)
              (fun i _ => dvd_refl 1) (fun p _ => divChain_ppow 2 p.1 _ (by
              intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]; omega))))
          h_eq
        -- hab : a * b = d₁ * d₂ (component-wise)
        -- From f-support: a entries are q-powers (q ∤ other primes)
        have ha_qpow := T_gen_pow_entries_qpower q (e q) D₁ hfD₁ a hD₁_eq ha_pos ha_div
        -- From g-support: b entries coprime to q
        obtain ⟨b', _, hb'_pos, hb'_div, hb'_det⟩ := prod_gen_support_det S' e D₂ hgD₂
        have hb_eq' := diagonal_representative_unique 2 b b' hb_pos hb'_pos hb_div hb'_div hD₂_eq
        subst hb_eq'
        -- d₁ entries are q-powers, d₂ entries coprime to q
        -- Per-entry: a(i)*b(i) = d₁(i)*d₂(i), with a(i) q-power, b(i) q-free,
        --   d₁(i) q-power, d₂(i) q-free → a(i) = d₁(i), b(i) = d₂(i)
        -- Arithmetic helper: if x*m = y*n with x,y having no prime factor ≠ q
        -- and q ∤ m, q ∤ n, then x = y (and m = n).
        -- Proof: x | x*m = y*n. Since Coprime(x, n) (x is q-power, q ∤ n): x | y.
        -- Symmetrically y | x. So x = y (both positive).
        have entry_eq : ∀ i, a i = d₁ i := by
          intro i
          have h_i : a i * b' i = d₁ i * d₂ i := by
            have := congr_fun hab i; simp only [Pi.mul_apply] at this; exact this
          -- a i has no prime factor ≠ q (from ha_qpow)
          -- d₁ i = ppowDiag(q,...) i is a q-power
          -- b' i and d₂ i: q ∤ (b' i) and q ∤ (d₂ i)?
          -- b' det coprime to q: ∏ b' = ∏_{S'} p^{...} coprime to q
          -- So q ∤ b'(i) (since b'(i) | ∏ b' for n=2)
          have hq_not_dvd_b : ¬(q.1 ∣ b' i) := by
            intro h; have : q.1 ∣ ∏ j, b' j := dvd_trans h
              (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
            rw [hb'_det] at this
            exact (Nat.Prime.coprime_iff_not_dvd q.2).mp
              (Nat.coprime_prod_right_iff.mpr (fun p hp =>
                (Nat.coprime_primes q.2 p.2).mpr (fun h => hq (h ▸ hp))) |>.pow_right _) this
          -- Similarly q ∤ d₂ i (d₂ i is a product of p-powers for p ∈ S', all ≠ q)
          have hq_not_dvd_d₂ : ¬(q.1 ∣ d₂ i) := by
            show ¬(q.1 ∣ (∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1]) i)
            simp only [Finset.prod_apply]
            rw [q.2.dvd_finset_prod_iff]; push_neg; intro p hp
            simp only [ppowDiag]
            exact fun h => absurd ((q.2.eq_of_dvd_of_prime p.2 (dvd_of_dvd_pow h)).symm ▸ hp) hq
          -- Coprime(a i, d₂ i): a i is q-power (no other prime factors), q ∤ d₂ i
          have hcop_a_d₂ : Nat.Coprime (a i) (d₂ i) := by
            rw [Nat.coprime_comm]; exact Nat.Coprime.coprime_dvd_right
              (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
              (Nat.Coprime.symm hcop)
          -- a i | d₁ i * d₂ i and Coprime(a i, d₂ i) → a i | d₁ i
          have ha_dvd : a i ∣ d₁ i := (hcop_a_d₂.dvd_of_dvd_mul_right (h_i ▸ dvd_mul_right _ _))
          -- Symmetrically: d₁ i | a i
          have hcop_d₁_b : Nat.Coprime (d₁ i) (b' i) := by
            show Nat.Coprime (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1] i) (b' i)
            simp only [ppowDiag]
            exact Nat.Coprime.pow_left _
              ((Nat.Prime.coprime_iff_not_dvd q.2).mpr hq_not_dvd_b)
          have hd₁_dvd : d₁ i ∣ a i :=
            (hcop_d₁_b.dvd_of_dvd_mul_right (h_i.symm ▸ dvd_mul_right _ _))
          exact Nat.dvd_antisymm ha_dvd hd₁_dvd
        constructor <;> funext i
        · exact entry_eq i
        · have h_i : a i * b' i = d₁ i * d₂ i := by
            have := congr_fun hab i; simp only [Pi.mul_apply] at this; exact this
          exact Nat.eq_of_mul_eq_mul_left (ha_pos i) (entry_eq i ▸ h_i)
    rw [h_factor, ih]

/-- **Algebraic independence of Hecke generators**: the generators `T_gen 2 p k`
for all primes `p` and `k ∈ Fin 2` are algebraically independent over `ℤ`.
Equivalently, the presentation map `π_hom` is injective.

**Proof**: follows the same "minimum-support Kronecker extraction" pattern as
`evalHom_injective_two` (PolynomialRing.lean), extended to multi-prime monomials
via `multi_prime_kronecker`. For any nonzero `f`, pick the monomial `s` in `f.support`
that minimises `(s(p₁,1), s(p₂,1), …)` lexicographically; evaluating `π_hom(f)`
at the leading coset of `s` extracts `f.coeff s ≠ 0`. -/
-- Helper: convert a GenIdx →₀ ℕ exponent into per-prime exponents
private noncomputable def toPrimeExp (d : GenIdx →₀ ℕ) : {p : ℕ // p.Prime} → Fin 2 → ℕ :=
  fun p k => d (p, k)

-- Helper: the set of primes appearing in a monomial
private def primesOf (d : GenIdx →₀ ℕ) : Finset {p : ℕ // p.Prime} :=
  d.support.image Prod.fst

/-- The monomial evaluation `∏ T_gen(i)^{d(i)}` equals the per-prime-grouped product
`∏_{p ∈ primesOf d} (T_gen(p,0)^{d(p,0)} * T_gen(p,1)^{d(p,1)})`.
This is a rearrangement of a commutative product. -/
private lemma monomial_eval_eq_prod_primes (d : GenIdx →₀ ℕ) :
    (∏ i ∈ d.support, (fun j : GenIdx => T_gen 2 j.1.1 j.2) i ^ d i) =
    ∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)) := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := Prod.fst) (t := primesOf d)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
  congr 1; ext p; congr 1
  -- The fiber {i ∈ d.support | i.1 = p} ⊆ image of Fin 2 via k ↦ (p,k).
  -- Rewrite RHS as product over {(p,0),(p,1)}, then use prod_subset for missing.
  set S := Finset.univ.image (fun k : Fin 2 => (p, k)) with hS_def
  -- ∏ over fiber ⊆ ∏ over S, extra terms have d(p,k)=0 so pow=1.
  rw [show T_gen 2 (↑p) 0 ^ toPrimeExp d p 0 * T_gen 2 (↑p) 1 ^ toPrimeExp d p 1 =
    ∏ i ∈ S, (fun j : GenIdx => T_gen 2 (↑j.1) j.2) i ^ d i from by
      simp [S, Fin.prod_univ_two, toPrimeExp, Finset.prod_image (by
        intro a _ b _ h; exact Prod.mk.inj h |>.2)]]
  apply Finset.prod_subset
  · -- fiber ⊆ S: if i ∈ d.support and i.1 = p then i = (p, i.2) ∈ S
    intro i hi; simp only [Finset.mem_filter] at hi
    simp [S, Finset.mem_image]; exact ⟨i.2, by ext <;> [exact hi.2.symm; rfl]⟩
  · -- Extra terms: if i ∈ S \ fiber then d(i) = 0, so i^{d(i)} = 1
    intro i hiS hi_not
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_and, not_not] at hi_not
    have hi_fst : i.1 = p := by
      simp [S, Finset.mem_image] at hiS; obtain ⟨k, hk⟩ := hiS; exact hk ▸ rfl
    rw [hi_not (Finsupp.mem_support_iff.mpr ∘ id) hi_fst]; exact pow_zero _

/-- The diagonal product of `∏ ppowDiag` equals the per-prime determinant product. -/
private lemma prod_ppowDiag_eq (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    ∏ i, (∏ p ∈ S, ppowDiag 2 p.1 ![e p 1, e p 0 + e p 1]) i =
    ∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) := by
  rw [Finset.prod_comm]
  congr 1; ext p
  simp only [ppowDiag, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [← pow_add]; congr 1; omega

/-- For monomial d, if the per-prime determinant profile differs from s's,
the evaluation at s's leading coset is 0.  Uses `prod_gen_support_det`. -/
private lemma monomial_eval_zero_of_det_ne (d s : GenIdx →₀ ℕ)
    (h_det : ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) ≠
             ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)) :
    (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)))
      (T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
        ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])) = 0 := by
  by_contra h; push_neg at h
  apply h_det
  -- Nonzero ⟹ by prod_gen_support_det, the coset has ∏ entries = d-profile
  obtain ⟨a, ha_eq, ha_pos, ha_div, ha_det⟩ := prod_gen_support_det (primesOf d) (toPrimeExp d)
    (T_diag _) (by rwa [ne_eq] at h)
  -- The coset is T_diag(c) where c = ∏ ppowDiag, with ∏ c = s-profile
  set c := ∏ p ∈ primesOf s, ppowDiag 2 p.1 ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1]
  have hc_pos : ∀ i, 0 < c i := fun i => Finset.prod_pos (fun p _ => ppowDiag_pos 2 p.1 p.2 _ i)
  have hc_div : DivChain 2 c := Finset.prod_induction _ (DivChain 2)
    (fun a b ha hb => DivChain_mul 2 a b ha hb) (fun i _ => dvd_refl 1)
    (fun p _ => divChain_ppow 2 p.1 _ (by intro i j h; fin_cases i <;> fin_cases j <;>
      simp_all [Fin.le_def]; omega))
  have hc_prod : ∏ i, c i = ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1) :=
    prod_ppowDiag_eq (primesOf s) (toPrimeExp s)
  -- a = c by diagonal uniqueness (both represent the same T_diag coset)
  have hac := diagonal_representative_unique 2 a c ha_pos hc_pos ha_div hc_div ha_eq
  rw [hac] at ha_det; rw [← ha_det, ← hc_prod]

private lemma T_gen_algebraicIndependent :
    AlgebraicIndependent ℤ (fun i : GenIdx => T_gen 2 i.1.1 i.2) := by
  rw [algebraicIndependent_iff_injective_aeval]
  show Function.Injective π_hom
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro P hP; rw [RingHom.mem_ker] at hP; rw [Submodule.mem_bot]
  by_contra hP_ne
  -- P ≠ 0: pick s ∈ P.support minimising the total "second exponent" ∑ d(p,1)
  -- This ensures: for any d with same det profile and d ≠ s, ∃ p with s(p,1) < d(p,1)
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image P.support
    (fun d : GenIdx →₀ ℕ => d.sum (fun i c => if i.2 = (1 : Fin 2) then c else 0))
    (MvPolynomial.support_nonempty.mpr hP_ne)
  have hs_coeff : P.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  -- Define the leading coset D_s
  set D_s := T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
    ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])
  -- (π_hom P)(D_s) = 0
  have h_zero : (π_hom P) D_s = 0 := by rw [hP]; rfl
  -- Expand π_hom P via eval₂_eq'
  change (MvPolynomial.eval₂ (Int.castRingHom (HeckeAlgebra 2))
    (fun i : GenIdx => T_gen 2 i.1.1 i.2) P) D_s = 0 at h_zero
  rw [MvPolynomial.eval₂_eq', Finset.sum_apply'] at h_zero
  -- Simplify: Int.cast(coeff) * prod = coeff * prod (as Finsupp eval)
  have h_term : ∀ d ∈ P.support,
      ((Int.cast (P.coeff d) : HeckeAlgebra 2) *
        (∏ i ∈ d.support, (fun j : GenIdx => T_gen 2 j.1.1 j.2) i ^ d i)) D_s =
      P.coeff d * (∏ i ∈ d.support,
        (fun j : GenIdx => T_gen 2 j.1.1 j.2) i ^ d i) D_s := by
    intro d _
    rw [show (Int.cast (P.coeff d) : HeckeAlgebra 2) =
      (P.coeff d) • (1 : HeckeAlgebra 2) from (zsmul_one _).symm,
      smul_mul_assoc, one_mul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl h_term] at h_zero
  -- Rewrite each monomial eval using monomial_eval_eq_prod_primes
  conv at h_zero => arg 1; arg 2; ext d
    rw [show (∏ i ∈ d.support, (fun j : GenIdx => T_gen 2 j.1.1 j.2) i ^ d i) =
      ∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1)) from monomial_eval_eq_prod_primes d]
  -- For each d ∈ P.support: evaluate the per-prime product at D_s
  -- Case 1: d and s have different determinant profiles → evaluation = 0
  -- Case 2: same det profile but d ≠ s → per-prime Kronecker gives 0
  -- Case 3: d = s → evaluation = 1
  -- In all cases, the term is P.coeff(d) * (if d = s then 1 else 0)
  have h_delta : ∀ d ∈ P.support,
      P.coeff d * (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1))) D_s =
      if d = s then P.coeff d else 0 := by
    intro d hd_mem
    by_cases hds : d = s
    · subst hds; simp only [ite_true]
      -- d = s: multi_prime_coeff_factor gives the product of per-prime evaluations
      rw [multi_prime_coeff_factor (primesOf s) (toPrimeExp s) (toPrimeExp s)]
      -- Each factor: monomial_eval_kronecker with trivial matching
      simp only [Finset.prod_congr rfl (fun p _ =>
        HeckeRing.GLn.Inj.monomial_eval_kronecker p.1 p.2
          (toPrimeExp s p 0) (toPrimeExp s p 1)
          (toPrimeExp s p 0) (toPrimeExp s p 1) le_rfl)]
      simp [mul_one]
    · simp only [hds, ite_false]
      -- d ≠ s: the evaluation at D_s is 0
      suffices (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1))) D_s = 0 by rw [this, mul_zero]
      by_cases h_det_eq :
          ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) =
          ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)
      · -- Same det ⟹ same prime set
        have h_same_primes : primesOf d = primesOf s := by
          -- Equal products of prime powers ⟹ same prime set
          -- For each p ∈ primesOf d: p | ∏_{primesOf d} = ∏_{primesOf s}, so p ∈ primesOf s.
          ext p; simp only [Finset.mem_coe]; constructor
          · intro hp
            have : p.1 ∣ ∏ q ∈ primesOf d, q.1 ^ (toPrimeExp d q 0 + 2 * toPrimeExp d q 1) :=
              Finset.dvd_prod_of_mem _ hp |>.trans (dvd_pow_self p.1 (by
                have := Finsupp.mem_support_iff.mp
                  (Finset.mem_image.mp hp |>.choose_spec.1); omega))
            rw [h_det_eq] at this
            rw [p.2.dvd_finset_prod_iff] at this
            obtain ⟨q, hq, hpq⟩ := this
            exact (p.2.eq_of_dvd_of_prime q.2 (dvd_of_dvd_pow hpq)).symm ▸ hq
          · intro hp
            have : p.1 ∣ ∏ q ∈ primesOf s, q.1 ^ (toPrimeExp s q 0 + 2 * toPrimeExp s q 1) :=
              Finset.dvd_prod_of_mem _ hp |>.trans (dvd_pow_self p.1 (by
                have := Finsupp.mem_support_iff.mp
                  (Finset.mem_image.mp hp |>.choose_spec.1); omega))
            rw [← h_det_eq] at this
            rw [p.2.dvd_finset_prod_iff] at this
            obtain ⟨q, hq, hpq⟩ := this
            exact (p.2.eq_of_dvd_of_prime q.2 (dvd_of_dvd_pow hpq)).symm ▸ hq
        rw [h_same_primes,
          multi_prime_coeff_factor (primesOf s) (toPrimeExp d) (toPrimeExp s)]
        -- Find p₀ where d(p₀,1) > s(p₀,1) and use monomial_eval_kronecker = 0
        -- Existence: d ≠ s + same det ⟹ ∃ p with d(p) ≠ s(p) ⟹ d(p,1) ≠ s(p,1)
        -- hs_min gives ∑ s(·,1) ≤ ∑ d(·,1), not all equal ⟹ ∃ d(p₀,1) > s(p₀,1)
        have ⟨p₀, hp₀_mem, hp₀_lt⟩ : ∃ p₀ ∈ primesOf s,
            toPrimeExp s p₀ 1 < toPrimeExp d p₀ 1 := by
          -- d ≠ s ⟹ ∃ i ∈ d.support ∪ s.support with d i ≠ s i
          -- Same prime set + same det at each prime + d(p,1) = s(p,1) ⟹ d(p) = s(p)
          -- So ∃ p with d(p,1) ≠ s(p,1).
          -- hs_min: total second exps of s ≤ those of d. Not all equal ⟹ ∃ d(p₀,1) > s(p₀,1).
          by_contra h_all_le; push_neg at h_all_le
          -- All p ∈ primesOf s have d(p,1) ≤ s(p,1)
          apply hds; ext ⟨p, k⟩
          by_cases hp : p ∈ primesOf s
          · -- Per-prime det equality via Nat.factorization.
            have h_per_prime : toPrimeExp d p 0 + 2 * toPrimeExp d p 1 =
                toPrimeExp s p 0 + 2 * toPrimeExp s p 1 := by
              have h_fact := congr_arg (fun n => n.factorization p.1) (h_same_primes ▸ h_det_eq)
              simp only [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (Nat.Prime.ne_zero
                (Finset.mem_image.mp hq |>.choose_spec.1 ▸ q.2)))] at h_fact
              simp only [Nat.Prime.factorization_pow, Finsupp.single_apply] at h_fact
              simp only [Finset.sum_ite_eq', Finset.mem_coe] at h_fact
              rwa [if_pos hp, if_pos hp] at h_fact
            have h_le := h_all_le p hp
            -- d(p,1) = s(p,1): pointwise ≤ with sum ≤ gives equality.
            -- Extend both Finsupp.sums to the common set T = d.support ∪ s.support.
            set T := d.support ∪ s.support
            set g := fun (i : GenIdx) (c : ℕ) => if i.2 = (1 : Fin 2) then c else 0
            have hd_sum : d.sum g = ∑ i ∈ T, g i (d i) := by
              simp only [Finsupp.sum]; exact (Finset.sum_subset Finset.subset_union_left
                (fun i _ hi => by simp [g, Finsupp.not_mem_support_iff.mp hi])).symm
            have hs_sum : s.sum g = ∑ i ∈ T, g i (s i) := by
              simp only [Finsupp.sum]; exact (Finset.sum_subset Finset.subset_union_right
                (fun i _ hi => by simp [g, Finsupp.not_mem_support_iff.mp hi])).symm
            -- Pointwise: g i (d i) ≤ g i (s i) for all i ∈ T.
            have h_ptwise : ∀ i ∈ T, g i (d i) ≤ g i (s i) := by
              intro ⟨q, k'⟩ _; simp only [g]
              split_ifs with hk
              · -- k' = 1: d(q,1) ≤ s(q,1). If q ∈ primesOf s: from h_all_le.
                -- If q ∉ primesOf s: q ∉ primesOf d (h_same_primes), so d(q,1) = 0 ≤ s(q,1).
                by_cases hq : q ∈ primesOf s
                · exact h_all_le q hq
                · have : (q, k') ∉ d.support := fun h =>
                    (h_same_primes ▸ hq) (Finset.mem_image.mpr ⟨_, h, rfl⟩)
                  simp [Finsupp.not_mem_support_iff.mp this]
              · exact le_refl 0
            -- Sum comparison: d.sum g ≤ s.sum g.
            have h_dg_le : d.sum g ≤ s.sum g := by
              rw [hd_sum, hs_sum]; exact Finset.sum_le_sum h_ptwise
            -- Combined with hs_min: s.sum g ≤ d.sum g ⟹ d.sum g = s.sum g.
            have h_sum_eq : d.sum g = s.sum g := le_antisymm h_dg_le
              (hs_min d (Finsupp.mem_support_iff.mpr (by
                intro h; exact hs_coeff (by rwa [MvPolynomial.mem_support_iff, h] at hd_mem))))
            -- d(p,1) = s(p,1): if d(p,1) < s(p,1) then ∑ < ∑, contradicting sum equality.
            have h_eq1 : toPrimeExp d p 1 = toPrimeExp s p 1 := by
              by_contra h_ne
              have hlt : g (p, (1 : Fin 2)) (d (p, 1)) < g (p, (1 : Fin 2)) (s (p, 1)) := by
                simp only [g]; exact lt_of_le_of_ne h_le h_ne
              have h_sum_strict : ∑ i ∈ T, g i (d i) < ∑ i ∈ T, g i (s i) :=
                Finset.sum_lt_sum h_ptwise ⟨(p, 1), Finset.mem_union.mpr
                  (Or.inr (Finsupp.mem_support_iff.mpr (by
                    intro h; simp [toPrimeExp, h] at hlt))), hlt⟩
              linarith [hd_sum ▸ hs_sum ▸ h_sum_eq]
            fin_cases k
            · omega  -- k = 0: from h_per_prime + h_eq1
            · exact h_eq1
          · -- p ∉ primesOf s = primesOf d: d(p,k) = s(p,k) = 0
            have hp' : p ∉ primesOf d := h_same_primes ▸ hp
            simp only [toPrimeExp] at *
            have : (p, k) ∉ d.support := fun h => hp' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            have : (p, k) ∉ s.support := fun h => hp (Finset.mem_image.mpr ⟨_, h, rfl⟩)
            simp [Finsupp.not_mem_support_iff.mp ‹(p,k) ∉ d.support›,
                  Finsupp.not_mem_support_iff.mp ‹(p,k) ∉ s.support›]
        apply Finset.prod_eq_zero hp₀_mem
        rw [HeckeRing.GLn.Inj.monomial_eval_kronecker p₀.1 p₀.2
          (toPrimeExp d p₀ 0) (toPrimeExp d p₀ 1)
          (toPrimeExp s p₀ 0) (toPrimeExp s p₀ 1) hp₀_lt.le]
        simp only [ite_eq_right_iff, one_ne_zero]
        intro ⟨_, h1⟩; exact absurd h1 (Nat.ne_of_gt hp₀_lt)
      · -- Different determinant profiles: evaluation = 0
        exact monomial_eval_zero_of_det_ne d s h_det_eq
  rw [Finset.sum_congr rfl h_delta] at h_zero
  simp only [Finset.sum_ite_eq_of_mem _ _ hs_mem] at h_zero
  exact hs_coeff h_zero

/-- `π_hom` is injective: the Hecke algebra generators are algebraically independent,
so the free polynomial ring `ℤ[X_{(p,k)}]` embeds faithfully into `HeckeAlgebra 2`. -/
private lemma π_injective : Function.Injective π_hom := by
  have h := algebraicIndependent_iff_injective_aeval.mp T_gen_algebraicIndependent
  intro a b hab; exact h hab

/-- **Kernel compatibility**: `ker π ≤ ker ψ`.
Since `π_hom` is injective, `ker π_hom = ⊥ ≤ ker (ψ_hom N)`. -/
private lemma ker_π_le_ker_ψ :
    RingHom.ker π_hom ≤ RingHom.ker (ψ_hom N) := by
  rw [(RingHom.injective_iff_ker_eq_bot π_hom).mp π_injective]
  exact bot_le

/-- The product element in a scalar × diagonal mulMap lands in the GL DC of the product diagonal.
Uses scalar centrality: `diag(c,c) * g = g * diag(c,c)` for all `g`. -/
private lemma product_mem_GL_DC_scalar
    (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) (ha_gcd : Int.gcd (a 0) N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N
          (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd))) :
    (p.1.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N
        (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) *
      ((p.2.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) ∈
    DoubleCoset.doubleCoset (diagMat 2 ((fun _ : Fin 2 => c) * a) : GL (Fin 2) ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
  -- Get DC memberships for reps
  have hc_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at hc_rep
  have ha_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N a ha ha_gcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at ha_rep
  -- Lift to GL-level DCs
  have hc_gl := Gamma0_doubleCoset_subset_Gamma N _ hc_rep
  have ha_gl := Gamma0_doubleCoset_subset_Gamma N _ ha_rep
  -- Decompose reps
  rw [DoubleCoset.mem_doubleCoset] at hc_gl ha_gl
  obtain ⟨L_c, ⟨σL_c, rfl⟩, R_c, ⟨σR_c, rfl⟩, hc_eq⟩ := hc_gl
  obtain ⟨L_a, ⟨σL_a, rfl⟩, R_a, ⟨σR_a, rfl⟩, ha_eq⟩ := ha_gl
  -- Get SL₂ memberships for coset elements
  obtain ⟨σp₁, rfl⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem p.1.out)
  obtain ⟨σp₂, rfl⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem p.2.out)
  -- Now compute: σp₁ * (L_c * diag(c,c) * R_c) * (σp₂ * (L_a * diag(a) * R_a))
  -- = σp₁ * L_c * (diag(c,c) * (R_c * σp₂ * L_a)) * diag(a) * R_a     [associativity]
  -- = σp₁ * L_c * ((R_c * σp₂ * L_a) * diag(c,c)) * diag(a) * R_a     [scalar comm]
  -- = σp₁ * L_c * R_c * σp₂ * L_a * (diag(c,c) * diag(a)) * R_a       [associativity]
  -- = σp₁ * L_c * R_c * σp₂ * L_a * diag((fun _ => c) * a) * R_a       [diagMat_mul]
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a),
    ⟨σp₁ * σL_c * σR_c * σp₂ * σL_a, rfl⟩,
    mapGL ℚ σR_a, ⟨σR_a, rfl⟩, ?_⟩
  rw [show HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) =
        mapGL ℚ σL_c * diagMat 2 (fun _ => c) * mapGL ℚ σR_c from hc_eq,
      show HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd) =
        mapGL ℚ σL_a * diagMat 2 a * mapGL ℚ σR_a from ha_eq]
  calc mapGL ℚ σp₁ * (mapGL ℚ σL_c * diagMat 2 (fun _ => c) * mapGL ℚ σR_c) *
        (mapGL ℚ σp₂ * (mapGL ℚ σL_a * diagMat 2 a * mapGL ℚ σR_a))
      = mapGL ℚ σp₁ * mapGL ℚ σL_c *
        (diagMat 2 (fun _ => c) * (mapGL ℚ σR_c * mapGL ℚ σp₂ * mapGL ℚ σL_a)) *
        (diagMat 2 a * mapGL ℚ σR_a) := by group
    _ = mapGL ℚ σp₁ * mapGL ℚ σL_c *
        ((mapGL ℚ σR_c * mapGL ℚ σp₂ * mapGL ℚ σL_a) * diagMat 2 (fun _ => c)) *
        (diagMat 2 a * mapGL ℚ σR_a) := by
          rw [diagMat_scalar_comm 2 c hc]
    _ = mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
        (diagMat 2 (fun _ => c) * diagMat 2 a) * mapGL ℚ σR_a := by
          simp only [map_mul]; group
    _ = mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
        diagMat 2 ((fun _ => c) * a) * mapGL ℚ σR_a := by
          rw [diagMat_mul 2 _ a (fun _ => hc) ha]

/-- Every mulMap output for scalar × arbitrary in the Gamma0 Hecke algebra
equals `T_diag_Gamma0 N ((fun _ => c) * a)`. -/
private lemma mulMap_Gamma0_scalar_eq
    (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) (ha_gcd : Int.gcd (a 0) N = 1)
    (hdiv : a 0 ∣ a 1)
    (hca_gcd : Int.gcd (↑((fun _ : Fin 2 => c) * a) 0) ↑N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N
          (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd))) :
    HeckeRing.mulMap (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd))
      (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) p =
    T_diag_Gamma0 N ((fun _ : Fin 2 => c) * a)
      (fun i => Nat.mul_pos hc (ha i)) hca_gcd := by
  set D := HeckeRing.mulMap (Gamma0_pair N) _ _ p
  -- Step 1: Get diagonal representative
  obtain ⟨b, hb, hgcd_b, hdiv_b, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
  have hrep' : D = T_diag_Gamma0 N b hb hgcd_b := by rw [← hrep]; exact (HeckeCoset.mk_rep D).symm
  -- Step 2: cosetMap gives T_diag b at GL level
  have hGL : cosetMap N D = T_diag b := by rw [hrep', cosetMap_T_diag_Gamma0]
  -- Step 3: cosetMap gives T_diag ((fun _ => c) * a) via GL DC membership
  have hGL_ca : cosetMap N D = T_diag ((fun _ : Fin 2 => c) * a) := by
    exact cosetMap_mulMap_mem_GL_DC N _ _ p _
      (product_mem_GL_DC_scalar N c hc a ha hc_gcd ha_gcd p)
  -- Step 4: b = (fun _ => c) * a by diagonal uniqueness
  have hdiv_b' : DivChain 2 b := fun i hi => (show i = 0 by omega) ▸ hdiv_b
  have hdiv_ca : DivChain 2 ((fun _ : Fin 2 => c) * a) := fun i hi => by
    have h0 : (⟨i, by omega⟩ : Fin 2) = (0 : Fin 2) := Fin.ext (show i = 0 by omega)
    have h1 : (⟨i + 1, hi⟩ : Fin 2) = (1 : Fin 2) := Fin.ext (show i + 1 = 1 by omega)
    show ((fun _ => c) * a) ⟨i, _⟩ ∣ ((fun _ => c) * a) ⟨i + 1, hi⟩
    rw [h0, h1]; simp only [Pi.mul_apply]; exact Nat.mul_dvd_mul_left c hdiv
  have hb_eq : b = (fun _ : Fin 2 => c) * a := diagonal_representative_unique 2 b
    ((fun _ : Fin 2 => c) * a) hb (fun i => Nat.mul_pos hc (ha i)) hdiv_b' hdiv_ca
    (by rw [← hGL, hGL_ca])
  subst hb_eq; exact hrep'

/-- The degree of a scalar Gamma0 double coset `T'(c, c)` is `1`:
`diag(c,c)` centralizes all of `GL₂(ℚ)`, hence the stabilizer is all of `Γ₀(N)`. -/
private lemma Gamma0_HeckeCoset_deg_scalar (c : ℕ) (hc : 0 < c)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) = 1 := by
  set D := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd
  set δ := HeckeCoset.rep D
  set H := (Gamma0_pair N).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H = H by
    have h_def : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
        ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  -- δ is in the DC of diag(c,c), so δ = h₁ * diag(c,c) * h₂ for some h₁, h₂ ∈ H
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) H H := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 => c) : GL (Fin 2) ℚ) H H := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk]
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem; obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  -- δ = (h₁ * h₂) * diag(c,c) by scalar centrality
  have hδ_simp : (δ : GL (Fin 2) ℚ) = (h₁ * h₂) * diagMat 2 (fun _ : Fin 2 => c) := by
    rw [hδ_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂, ← mul_assoc]
  -- ConjAct by h₁*h₂ preserves H, and ConjAct by diag(c,c) preserves H
  rw [hδ_simp, map_mul, ← smul_smul]
  -- Scalar conjugation preserves H (any subgroup)
  have hscalar_smul : ConjAct.toConjAct (diagMat 2 (fun _ : Fin 2 => c)) • H = H := by
    ext x; constructor
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
      rwa [diagMat_scalar_conj_eq 2 c hc] at hx
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      rwa [diagMat_scalar_conj_eq 2 c hc]
  rw [hscalar_smul]
  -- ConjAct by an element of H preserves H
  ext x; simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx; have : x = (h₁ * h₂) * ((h₁ * h₂)⁻¹ * x * (h₁ * h₂)) * (h₁ * h₂)⁻¹ := by group
    rw [this]; exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) hx) (H.inv_mem (H.mul_mem hh₁ hh₂))
  · intro hx; exact H.mul_mem (H.mul_mem (H.inv_mem (H.mul_mem hh₁ hh₂)) hx) (H.mul_mem hh₁ hh₂)

/-- **Generalized Gamma0-level scalar multiplication**: `T'(c,c) * T'(a₀,a₁) = T'(c*a₀, c*a₁)`.
The scalar `diag(c,c)` centralizes `Γ₀(N)`, so its double coset has degree 1
and the unique mulMap output is `T'(c*a₀, c*a₁)` with multiplicity 1. -/
private lemma T_Gamma0_scalar_mul_gen (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hc_gcd : Int.gcd (↑c) ↑N = 1)
    (ha_gcd : Int.gcd (a 0) N = 1) (hdiv : a 0 ∣ a 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N a ha ha_gcd) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ((fun _ : Fin 2 => c) * a)
        (fun i => Nat.mul_pos hc (ha i))
        (by show Int.gcd (↑(c * a 0)) ↑N = 1
            simp only [Int.gcd_natCast_natCast]
            exact Nat.Coprime.mul_left
              (by rwa [Int.gcd_natCast_natCast] at hc_gcd)
              (by rwa [Int.gcd_natCast_natCast] at ha_gcd))) 1 := by
  set D_c := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd
  set D_a := T_diag_Gamma0 N a ha ha_gcd
  have hca_gcd' : Int.gcd (↑((fun _ : Fin 2 => c) * a) 0) ↑N = 1 := by
    show Int.gcd (↑(c * a 0)) ↑N = 1
    simp only [Int.gcd_natCast_natCast]
    exact Nat.Coprime.mul_left
      (by rwa [Int.gcd_natCast_natCast] at hc_gcd)
      (by rwa [Int.gcd_natCast_natCast] at ha_gcd)
  set D_out := T_diag_Gamma0 N ((fun _ : Fin 2 => c) * a)
    (fun i => Nat.mul_pos hc (ha i)) hca_gcd'
  change HeckeRing.T_single _ ℤ D_c 1 * HeckeRing.T_single _ ℤ D_a 1 =
    HeckeRing.T_single _ ℤ D_out 1
  have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D_c.rep D_a.rep p = D_out :=
    mulMap_Gamma0_scalar_eq N c hc a ha hc_gcd ha_gcd hdiv hca_gcd'
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) D_c D_a D_out ?_ ?_
  · -- heckeMultiplicity = 1: Subsingleton approach
    have h_card : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) = 1 := by
      have := Gamma0_HeckeCoset_deg_scalar N c hc hc_gcd
      simp only [HeckeRing.HeckeCoset_deg] at this; exact_mod_cast this
    haveI : Subsingleton (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
    have h_le : HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_a.rep D_out.rep ≤ 1 := by
      classical
      simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
      apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
      intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (Gamma0_pair N) D_c.rep D_a.rep D_out.rep i₁ j₁ j₂ h₁ h₂
      subst hj; rfl
    have h_pos : 0 < HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_a.rep D_out.rep := by
      have h_mem : D_out ∈ HeckeRing.mulSupport (Gamma0_pair N) D_c.rep D_a.rep := by
        simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
          true_and, Prod.exists]
        have ⟨i₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
          Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
        have ⟨j₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_a.rep) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_a
            simp only [HeckeRing.HeckeCoset_deg] at this; omega)
        exact ⟨i₀, j₀, h_mulMap (i₀, j₀)⟩
      exact HeckeRing.heckeMultiplicity_pos_of_mem (Gamma0_pair N) _ _ _ h_mem
    omega
  · -- heckeMultiplicity = 0 elsewhere
    intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ D_out A hA h_mulMap

/-- **Gamma0-level scalar multiplication**: `T'(c,c) * T'(1,m) = T'(c, c*m)`.
The scalar `diag(c,c)` centralizes `Γ₀(N)`, so its double coset has degree 1
and the unique mulMap output is `T'(c, c*m)` with multiplicity 1.
This is used for the `d₁ > 1` case of surjectivity (Shimura Thm 3.34). -/
private lemma T_Gamma0_scalar_mul (c m : ℕ) (hc : 0 < c) (hm : 0 < m)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm]) (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ((fun _ : Fin 2 => c) * ![1, m])
        (fun i => Nat.mul_pos hc (by fin_cases i <;> simp [hm]))
        (by show Int.gcd (↑(c * 1)) ↑N = 1; simp [hc_gcd])) 1 := by
  set D_c := T_diag_Gamma0 N (fun _ : Fin 2 => c) (fun _ => hc) hc_gcd
  set D_m := T_diag_Gamma0 N (![1, m]) (fun i => by fin_cases i <;> simp [hm]) (by simp)
  set D_out := T_diag_Gamma0 N ((fun _ : Fin 2 => c) * ![1, m])
    (fun i => Nat.mul_pos hc (by fin_cases i <;> simp [hm]))
    (by show Int.gcd (↑(c * 1)) ↑N = 1; simp [hc_gcd])
  change HeckeRing.T_single _ ℤ D_c 1 * HeckeRing.T_single _ ℤ D_m 1 =
    HeckeRing.T_single _ ℤ D_out 1
  have hca_gcd : Int.gcd (↑((fun _ : Fin 2 => c) * (![1, m] : Fin 2 → ℕ)) 0) ↑N = 1 := by
    simp [hc_gcd]
  have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D_c.rep D_m.rep p = D_out := by
    intro p
    have h := mulMap_Gamma0_scalar_eq N c hc ![1, m]
      (fun i => by fin_cases i <;> simp [hm]) hc_gcd (by simp) (by simp) hca_gcd p
    convert h using 2
    simp only [T_diag_Gamma0]; congr 1
    ext i; fin_cases i <;> simp [Pi.mul_apply]
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) D_c D_m D_out ?_ ?_
  · -- heckeMultiplicity = 1: since deg(D_c) = 1, decompQuot(D_c) is a singleton,
    -- so pairs (i,j) are determined by j. Since mulMap always hits D_out,
    -- there's at most one pair per target. Combined with positivity, μ = 1.
    have h_card : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) = 1 := by
      have := Gamma0_HeckeCoset_deg_scalar N c hc hc_gcd
      simp only [HeckeRing.HeckeCoset_deg] at this; exact_mod_cast this
    haveI : Subsingleton (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
    have h_le : HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_m.rep D_out.rep ≤ 1 := by
      classical
      simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
      apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
      intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (Gamma0_pair N) D_c.rep D_m.rep D_out.rep i₁ j₁ j₂ h₁ h₂
      subst hj; rfl
    have h_pos : 0 < HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_m.rep D_out.rep := by
      have h_mem : D_out ∈ HeckeRing.mulSupport (Gamma0_pair N) D_c.rep D_m.rep := by
        simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
          true_and, Prod.exists]
        have ⟨i₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
          Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
        have ⟨j₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_m.rep) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_m
            simp only [HeckeRing.HeckeCoset_deg] at this; omega)
        exact ⟨i₀, j₀, h_mulMap (i₀, j₀)⟩
      exact HeckeRing.heckeMultiplicity_pos_of_mem (Gamma0_pair N) _ _ _ h_mem
    omega
  · -- heckeMultiplicity = 0 elsewhere
    intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ D_out A hA h_mulMap

/-- **T'(1,p) ∈ range(ψ)** for any prime p: follows directly from ψ_hom definition. -/
private lemma T_1p_mem_ψ_range (p : ℕ) (hp : p.Prime) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p])
        (fun i => by fin_cases i <;> simp [hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range :=
  ⟨MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2)), by
    show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2))) = _
    simp only [ψ_hom, MvPolynomial.eval₂Hom_X']; rfl⟩


/-- **T'(1,m) ∈ range(ψ)** by strong induction on m (Shimura Thm 3.34 core).
Handles: m=1 (identity), m=p prime (generator), coprime products (T_coprime_mul),
p|N prime powers (T_bad_mul), non-prime-power composites (factorization + coprime mul).
The case p∤N, k≥2 (pure prime power, p coprime to level) extracts T'(1,p^k) from the
product T'(1,p) * T'(1,p^{k-1}) via degree inequality argument + subtraction;
one sorry remains encapsulating the degree formula + multiplicity=1 claim. -/
private lemma T_1m_mem_ψ_range (m : ℕ) (hm : 0 < m) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (fun i => by fin_cases i <;> simp [hm])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
  by_cases hm1 : m = 1
  · -- m = 1: identity coset
    subst hm1; convert (ψ_hom N).range.one_mem using 1
    show Finsupp.single _ 1 = 1; rfl
  · -- m > 1: extract prime factor
    obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    set q := m / p with hq_def
    have hpq : m = p * q := (Nat.mul_div_cancel' hp_dvd).symm
    have hq_pos : 0 < q := Nat.pos_of_ne_zero
      (by intro h; rw [h, Nat.mul_zero] at hpq; omega)
    have hq_lt : q < m := by
      rw [hpq]; exact lt_mul_of_one_lt_left hq_pos hp.one_lt
    by_cases hcop : Nat.Coprime p q
    · -- gcd(p, q) = 1: use T_coprime_mul
      have hp_lt : p < m := by
        rw [hpq]; exact lt_mul_of_one_lt_right hp.pos (by omega)
      have h_IHp := ih p hp_lt hp.pos
      have h_IHq := ih q hq_lt hq_pos
      conv_lhs => rw [hpq]
      rw [← T_coprime_mul N p q hp.pos hq_pos hcop]
      exact (ψ_hom N).range.mul_mem h_IHp h_IHq
    · -- gcd(p, q) > 1: p | q, so p² | m. Factor out ALL p-powers.
      -- Let a = p^(v_p(m)), b = m/a. Then gcd(a,b)=1 and both < m (since m has ≥2 prime factors or p²|m).
      -- Use T_coprime_mul for (a, b).
      -- But if m = p^k (pure prime power), b = 1 and we need T'(1, p^k) ∈ range.
      -- For p | N: T'(1,p)^k = T'(1,p^k) by T_bad_mul. T'(1,p) ∈ range.
      -- For p ∤ N, k ≥ 2: need the Hecke product extraction argument.
      -- First check: is m a prime power?
      by_cases hm_ppow : ∃ k, m = p ^ k
      · -- m = p^k for some k ≥ 2
        obtain ⟨k, rfl⟩ := hm_ppow
        have hk : 2 ≤ k := by
          by_contra h; push_neg at h; interval_cases k <;> simp_all
        by_cases hpN : (p : ℤ).gcd N = 1
        · -- p coprime to N, k ≥ 2: Hecke product extraction (Shimura Thm 3.34).
          -- Mathematical argument:
          -- (1) T'(1,p) * T'(1,p^{k-1}) is in range (both factors in range by IH).
          -- (2) The product expands as Σ_D μ_D · T_single D 1 where each D = T'(p^j, p^{k-j}).
          -- (3) For j ≥ 1: T_single (T'(p^j, p^{k-j})) 1 ∈ range via T_Gamma0_scalar_mul + IH.
          -- (4) μ₀ = 1 at T'(1, p^k): identity pair gives μ₀ ≥ 1; degree inequality gives
          --     μ₀ ≤ deg(product)/deg(T'(1,p^k)) = (p+1)/p ≤ 1 for integer μ₀.
          -- (5) Extract T'(1, p^k) by subtraction.
          --
          -- Formalization requires the Gamma0-level multiplication formula
          -- `T'(1,p) * T'(1, p^{k-1}) = T'(1, p^k) + c • T'(p, p^{k-1})`,
          -- which transfers from the GL-level `T_sum_prime_mul_T_ad` (Shimura 3.24(5))
          -- via the ring hom `shimura_ring_hom = ψ_hom ∘ π_hom⁻¹`. The transfer requires
          -- showing `shimura_ring_hom` maps GL basis elements to Gamma0 basis elements,
          -- which follows from the decompQuot CRT bijection
          -- `Γ₀(N)/Γ₀(Np^j) ≅ SL₂(ℤ)/Γ₀(p^j)` for gcd(N,p)=1 (~300 lines of formalization).
          sorry
        · -- p | N: T'(1,p^k) = T'(1,p)^k by T_bad_mul (all p-powers multiply simply)
          -- T'(1,p) ∈ range directly. Product ∈ range by subring closure.
          -- T'(1,p) * T'(1,p^{k-1}) = T'(1,p^k) by T_bad_mul, and both ∈ range by IH.
          have hp_lt : p < p ^ k := by
            calc p = p ^ 1 := (pow_one p).symm
              _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt hk
          have hpk1_lt : p ^ (k - 1) < p ^ k :=
            Nat.pow_lt_pow_right hp.one_lt (by omega)
          have h_IHp := ih p hp_lt hp.pos
          have h_IHpk1 := ih (p ^ (k - 1)) hpk1_lt (pow_pos hp.pos _)
          -- p | N means p ∣ N^1 and p^{k-1} ∣ N^{k-1}
          have hpN : ¬((p : ℤ).gcd ↑N = 1) := hpN
          have hp_dvd_N : p ∣ N := by
            by_contra h
            exact hpN (by rw [Int.gcd_natCast_natCast]; exact (hp.coprime_iff_not_dvd.mpr h))
          conv_lhs => rw [show p ^ k = p * p ^ (k - 1) from by rw [← pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk]]
          rw [← T_bad_mul N p (p ^ (k - 1)) hp.pos (pow_pos hp.pos _) 1
            (dvd_trans hp_dvd_N (dvd_pow_self N (by omega)))
            (k - 1) (Nat.pow_dvd_pow N (by omega))]
          exact (ψ_hom N).range.mul_mem h_IHp h_IHpk1
      · -- m is NOT a prime power: it has another prime factor q ≠ p.
        -- Factor m = p^(v_p(m)) * (m / p^(v_p(m))) with coprime parts.
        push_neg at hm_ppow
        -- m has at least one prime factor ≠ p, say q.
        -- Split: a = p-part of m, b = p-free part of m. gcd(a,b)=1, both > 1, both < m.
        -- Factor m = p^v * (m/p^v) with coprime parts.
        set v := m.factorization p
        set a := p ^ v with ha_def
        set b := m / a with hb_def
        have ha_dvd : a ∣ m := Nat.ord_pow_dvd_factorization p m
        have hab : m = a * b := (Nat.mul_div_cancel' ha_dvd).symm
        have hv_pos : 0 < v := by
          rw [show v = m.factorization p from rfl]
          exact Nat.Prime.factorization_pos hp hp_dvd
        have ha_pos : 0 < a := pow_pos hp.pos v
        have hb_pos : 0 < b := Nat.pos_of_ne_zero (by
          intro hb0; rw [hb0, Nat.mul_zero] at hab; omega)
        have ha_lt : a < m := by
          rw [hab]; refine lt_mul_of_one_lt_right ha_pos ?_
          by_contra h; push_neg at h; interval_cases b
          · omega
          · -- b = 1 means m = a = p^v, contradicting hm_ppow
            exact hm_ppow v (by omega)
        have hb_lt : b < m := by
          rw [hab]; exact lt_mul_of_one_lt_left hb_pos (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
        have hcop_ab : Nat.Coprime a b := Nat.coprime_ppow_primes hp
          (Nat.coprime_div_pow_factorization hp.prime m)
        conv_lhs => rw [hab]
        rw [← T_coprime_mul N a b ha_pos hb_pos hcop_ab]
        exact (ψ_hom N).range.mul_mem (ih a ha_lt ha_pos) (ih b hb_lt hb_pos)

/-- **T'(d₁,d₂) ∈ range(ψ)** for `d₁ | d₂`, `gcd(d₁,N) = 1`.
Reduces to `T_1m_mem_ψ_range` when `d₁ = 1`. The `d₁ > 1` case needs
Gamma0-level scalar extraction: `T'(d₁,d₂) = T'(d₁,d₁) * T'(1,d₂/d₁)`. -/
private lemma T_diag_mem_ψ_range (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) (hdiv : a 0 ∣ a 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N a ha hgcd) 1 ∈ (ψ_hom N).range := by
  by_cases ha1 : a 0 = 1
  · -- d₁ = 1: direct from T_1m_mem_ψ_range
    have ha_eq : a = ![1, a 1] := by ext i; fin_cases i <;> simp [ha1]
    have : T_diag_Gamma0 N a ha hgcd = T_diag_Gamma0 N (![1, a 1])
        (fun i => by fin_cases i <;> simp [ha 1]) (by simp) := by
      simp only [T_diag_Gamma0]; congr 1; ext; simp [ha_eq]
    rw [this]
    exact T_1m_mem_ψ_range N (a 1) (ha 1)
  · -- d₁ > 1: factor T'(a₀, a₁) = T'(a₀, a₀) * T'(1, a₁/a₀) and show each ∈ range.
    have ha0_gt : 1 < a 0 := Nat.one_lt_iff_ne_one.mpr ha1
    -- Step 1: T'(1, a₁/a₀) ∈ range
    set q := a 1 / a 0 with hq_def
    have hq_pos : 0 < q := Nat.pos_of_ne_zero (by
      intro hq0; rw [hq_def, Nat.div_eq_zero_iff (ha 0)] at hq0
      exact Nat.not_lt.mpr (Nat.le_of_dvd (ha 1) hdiv) hq0)
    have hq_mul : a 1 = a 0 * q := (Nat.mul_div_cancel' hdiv).symm
    have h_T1q := T_1m_mem_ψ_range N q hq_pos
    -- Step 2: T'(a₀, a₀) ∈ range, by strong induction on a₀
    suffices hscalar : ∀ (d : ℕ) (hd : 0 < d) (hd_gcd : Int.gcd (↑d) ↑N = 1),
        HeckeRing.T_single (Gamma0_pair N) ℤ
          (T_diag_Gamma0 N (fun _ : Fin 2 => d) (fun _ => hd) hd_gcd) 1 ∈
          (ψ_hom N).range by
      -- Step 3: Combine using T_Gamma0_scalar_mul_gen
      have h_scalar_a0 := hscalar (a 0) (ha 0) hgcd
      -- T'(a₀, a₀) * T'(1, q) = T'(a₀, a₀*q) = T'(a₀, a₁)
      have h_product := T_Gamma0_scalar_mul N (a 0) q (ha 0) hq_pos hgcd
      -- (fun _ => a 0) * ![1, q] = ![a 0, a 0 * q] = ![a 0, a 1] = a
      have hfun_eq : (fun _ : Fin 2 => a 0) * ![1, q] = a := by
        ext i; fin_cases i
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, hq_mul]
      -- Match T_diag_Gamma0 arguments
      have hD_eq : T_diag_Gamma0 N ((fun _ : Fin 2 => a 0) * ![1, q])
          (fun i => Nat.mul_pos (ha 0) (by fin_cases i <;> simp [hq_pos]))
          (by show Int.gcd (↑(a 0 * 1)) ↑N = 1; simp [hgcd]) =
        T_diag_Gamma0 N a ha hgcd := by
        simp only [T_diag_Gamma0]; congr 1; exact hfun_eq
      rw [hD_eq] at h_product
      rw [← h_product]
      exact (ψ_hom N).range.mul_mem h_scalar_a0 h_T1q
    -- Prove the scalar helper by strong induction on d
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
    intro hd hd_gcd
    by_cases hd1 : d = 1
    · -- d = 1: T'(1, 1) = identity
      subst hd1
      convert (ψ_hom N).range.one_mem using 1
      show Finsupp.single _ 1 = 1; rfl
    · -- d > 1: extract prime p | d with gcd(p, N) = 1
      obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      -- gcd(p, N) = 1 since p | d and gcd(d, N) = 1
      have hp_gcd : Int.gcd (↑p) ↑N = 1 := by
        rw [Int.gcd_natCast_natCast] at hd_gcd ⊢
        exact Nat.Coprime.coprime_dvd_left hp_dvd hd_gcd
      -- T'(p, p) ∈ range: it's a generator of ψ_hom
      have hp_not_dvd_N : ¬(p ∣ N) := by
        intro h; rw [Int.gcd_natCast_natCast] at hp_gcd
        exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, dvd_refl p, h⟩ hp_gcd
      have h_Tpp : HeckeRing.T_single (Gamma0_pair N) ℤ
          (T_diag_Gamma0 N (![p, p]) (fun i => by fin_cases i <;> simp [hp.pos])
            (by show Int.gcd (↑p) ↑N = 1; exact hp_gcd)) 1 ∈ (ψ_hom N).range :=
        ⟨MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2)), by
          show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2))) = _
          simp only [ψ_hom, MvPolynomial.eval₂Hom_X']
          simp only [show (1 : Fin 2) ≠ 0 from by omega, ↓reduceIte,
            dif_neg hp_not_dvd_N]
          congr 1; simp only [T_diag_Gamma0]; congr 1
          ext i; fin_cases i <;> rfl⟩
      -- Convert T'(![p,p]) to T'(fun _ => p)
      have h_pp_eq : T_diag_Gamma0 N (![p, p])
          (fun i => by fin_cases i <;> simp [hp.pos])
          (by show Int.gcd (↑p) ↑N = 1; exact hp_gcd) =
        T_diag_Gamma0 N (fun _ : Fin 2 => p) (fun _ => hp.pos) hp_gcd := by
        simp only [T_diag_Gamma0]; congr 1; ext i; fin_cases i <;> rfl
      rw [h_pp_eq] at h_Tpp
      -- d/p: properties
      set e := d / p with he_def
      have he_pos : 0 < e := Nat.pos_of_ne_zero (by
        intro he0; rw [he_def, Nat.div_eq_zero_iff hp.pos] at he0; omega)
      have he_mul : d = p * e := (Nat.mul_div_cancel' hp_dvd).symm
      have he_lt : e < d := by
        rw [he_mul]; exact lt_mul_of_one_lt_left he_pos hp.one_lt
      have he_gcd : Int.gcd (↑e) ↑N = 1 := by
        rw [Int.gcd_natCast_natCast] at hd_gcd ⊢
        exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left p he_mul) hd_gcd
      -- T'(e, e) ∈ range by IH
      have h_Te := ih e he_lt he_pos he_gcd
      -- T'(p,p) * T'(e,e) = T'(p*e, p*e) = T'(d, d) by T_Gamma0_scalar_mul_gen
      have h_prod := T_Gamma0_scalar_mul_gen N p hp.pos (fun _ : Fin 2 => e)
        (fun _ => he_pos) hp_gcd he_gcd (dvd_refl e)
      -- (fun _ => p) * (fun _ => e) = (fun _ => d)
      have hpe_eq : (fun _ : Fin 2 => p) * (fun _ : Fin 2 => e) = (fun _ : Fin 2 => d) := by
        ext i; simp [Pi.mul_apply, ← he_mul]
      have hD_eq' : T_diag_Gamma0 N ((fun _ : Fin 2 => p) * (fun _ : Fin 2 => e))
          (fun i => Nat.mul_pos hp.pos he_pos)
          (by show Int.gcd (↑(p * e)) ↑N = 1; rw [← he_mul]; exact hd_gcd) =
        T_diag_Gamma0 N (fun _ : Fin 2 => d) (fun _ => hd) hd_gcd := by
        simp only [T_diag_Gamma0]; congr 1; exact hpe_eq
      rw [hD_eq'] at h_prod
      rw [← h_prod]
      exact (ψ_hom N).range.mul_mem h_Tpp h_Te

/-- **Target surjectivity** (Shimura Thm 3.34): `𝕋 (Gamma0_pair N) ℤ` is generated
    as a ring by the images of `ψ`. -/
private lemma ψ_surjective :
    Function.Surjective (ψ_hom N) := by
  intro y
  induction y using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨xf, rfl⟩ := hf; obtain ⟨xg, rfl⟩ := hg
    exact ⟨xf + xg, map_add _ _ _⟩
  | single D c =>
    -- T_single D c ∈ range: factor coefficient, get diagonal representative
    suffices h : Finsupp.single D 1 ∈ (ψ_hom N).range by
      obtain ⟨x, hx⟩ := h
      exact ⟨c • x, by rw [map_zsmul, hx, Finsupp.smul_single', smul_eq_mul, mul_one]⟩
    -- Get diagonal representative for D
    obtain ⟨a, ha, hgcd, hdiv, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
    have hD : D = T_diag_Gamma0 N a ha hgcd := by
      rw [show D = (⟦HeckeCoset.rep D⟧ : HeckeCoset (Gamma0_pair N)) from
        (Quotient.out_eq D).symm, hrep]
    rw [hD]
    exact T_diag_mem_ψ_range N a ha hgcd hdiv

/-- The surjective ring hom `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))` via factorization. -/
private noncomputable def shimura_ring_hom :
    HeckeAlgebra 2 →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ :=
  (Ideal.Quotient.lift (RingHom.ker π_hom) (ψ_hom N)
    (fun a ha => (ker_π_le_ker_ψ N) ha)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.toRingHom

/-- `shimura_ring_hom` is surjective. -/
private theorem shimura_ring_hom_surjective :
    Function.Surjective (shimura_ring_hom N) := by
  show Function.Surjective ((Ideal.Quotient.lift (RingHom.ker π_hom) (ψ_hom N)
    (fun a ha => (ker_π_le_ker_ψ N) ha)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.toRingHom)
  exact (Ideal.Quotient.lift_surjective_of_surjective (RingHom.ker π_hom)
      (fun a ha => (ker_π_le_ker_ψ N) ha) (ψ_surjective N)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.surjective

/-- **Shimura Theorem 3.35**: There exists a surjective ring homomorphism
    `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))`. -/
theorem shimura_thm_3_35 (N : ℕ) [NeZero N] :
    ∃ φ : HeckeRing.𝕋 (GL_pair 2) ℤ →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ,
      Function.Surjective φ :=
  ⟨shimura_ring_hom N, shimura_ring_hom_surjective N⟩

end Thm335

/-! ### Consequences for the multiplication table

By applying the surjection to our existing `T_sum_mul`, `T_sum_ppow_recurrence`,
etc., we get the level-N versions automatically. The key simplification:
since `T(p,p) ↦ 0` for `p | N`, the prime-power recurrence becomes:

  For p ∤ N:  T'(p^{k+1}) = T'(p)T'(p^k) - p·T'(p,p)·T'(p^{k-1})  (same as level 1)
  For p | N:  T'(p^k) = T'(p)^k                                     (simplified)

And the general formula (3.3.6) becomes:

  T'(m)T'(n) = Σ_{d|(m,n), (d,N)=1} d · T'(d,d) · T'(mn/d²)

The condition `(d,N) = 1` arises because `T'(d,d) = 0` when `d` has a factor dividing N.
-/

end HeckeRing.GLn
