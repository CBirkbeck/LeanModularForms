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
import LeanModularForms.HeckeRIngs.GLn.PolynomialRing
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
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Foundation

Defines the Hecke pair `(Γ₀(N), Δ₀(N))` for congruence subgroups and the
foundational double-coset lemmas (Shimura §3.3, 3.28–3.29), including the
Chinese-remainder machinery `Gamma_gcd_eq_mul` and the coprime-determinant
double-coset comparison `doubleCoset_eq_of_Gamma0_coprimeDet`.

This is the base module of the `CongruenceHecke` chain.

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

lemma Delta0_le_posDetInt (N : ℕ) :
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
  have hσ_mem : σ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
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
  have hσ_mem : σ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
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
lemma Gamma0_le_SLnZ :
    (CongruenceSubgroup.Gamma0 N).map (mapGL ℚ) ≤ SLnZ_subgroup 2 := by
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨σ, _, rfl⟩ := hg
  exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩

/-- `Γ(N) ≤ Γ₀(N)`: the principal congruence subgroup is contained in Gamma0. -/
lemma GammaN_le_Gamma0 :
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

/-- The reduction modulo `m ∣ lcm(a,b)` of a lift `β` of an integer matrix `M`
    (reduced mod `lcm`) has entries `M i j` reduced mod `m`. Used to check
    `β ∈ Γ(a)` and `β⁻¹γ ∈ Γ(b)` from the single CRT lift in `Gamma_gcd_eq_mul`. -/
private lemma crt_lift_reduces_mod {a b : ℕ} [NeZero (Nat.lcm a b)]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (β : SpecialLinearGroup (Fin 2) ℤ)
    (hβ : (↑(SpecialLinearGroup.map (Int.castRingHom (ZMod (Nat.lcm a b))) β) :
        Matrix (Fin 2) (Fin 2) (ZMod (Nat.lcm a b))) =
      M.map (Int.castRingHom (ZMod (Nat.lcm a b))))
    {m : ℕ} (hm : m ∣ Nat.lcm a b) (i j : Fin 2) :
    (↑(SpecialLinearGroup.map (Int.castRingHom (ZMod m)) β) :
        Matrix (Fin 2) (Fin 2) (ZMod m)) i j = ((M i j : ℤ) : ZMod m) := by
  have hentry : (((β : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (Nat.lcm a b)) =
      ((M i j : ℤ) : ZMod (Nat.lcm a b)) := by
    have := congr_fun₂ hβ i j
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]
      using this
  have := congr_arg (ZMod.castHom hm (ZMod m)) hentry
  simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
    map_intCast] using this

/-- The hard direction of `Gamma_gcd_eq_mul`: any `γ ∈ Γ(gcd(a,b))` factors as
    `y * z` with `y ∈ Γ(a)` and `z ∈ Γ(b)`. A single Chinese-remainder lift `β`
    of the CRT-combined entries gives `y = β` and `z = β⁻¹γ`. -/
private lemma exists_Gamma_factor_of_mem_Gamma_gcd (a b : ℕ) [NeZero a] [NeZero b]
    [NeZero (Nat.gcd a b)] [NeZero (Nat.lcm a b)]
    (γ : SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma (Nat.gcd a b)) :
    ∃ y ∈ CongruenceSubgroup.Gamma a, ∃ z ∈ CongruenceSubgroup.Gamma b, y * z = γ := by
  have hcompat : ∀ i j : Fin 2,
      ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ℤ) ≡
      (γ i j : ℤ) [ZMOD ↑(Int.gcd (↑a) (↑b))] := by
    rw [show (↑(Int.gcd (↑a : ℤ) (↑b : ℤ)) : ℤ) = ↑(Nat.gcd a b) from by simp [Int.gcd]]
    exact SL2_gamma_entry_modEq _ γ hγ
  obtain ⟨z00, hz00a, hz00b⟩ := int_crt (hcompat 0 0)
  obtain ⟨z01, hz01a, hz01b⟩ := int_crt (hcompat 0 1)
  obtain ⟨z10, hz10a, hz10b⟩ := int_crt (hcompat 1 0)
  obtain ⟨z11, hz11a, hz11b⟩ := int_crt (hcompat 1 1)
  have hdet_lcm : z00 * z11 - z01 * z10 ≡ 1 [ZMOD ↑(Nat.lcm a b)] := by
    rw [show (↑(Nat.lcm a b) : ℤ) = ↑(Int.lcm ↑a ↑b) from by simp [Int.lcm, Nat.lcm]]
    rw [← Int.modEq_and_modEq_iff_modEq_lcm]
    refine ⟨?_, ?_⟩
    · show z00 * z11 - z01 * z10 ≡ 1 * 1 - 0 * 0 [ZMOD ↑a]
      exact (hz00a.mul hz11a).sub (hz01a.mul hz10a)
    · have hdetγ : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := γ.prop; rw [det_fin_two] at h; exact_mod_cast h
      show z00 * z11 - z01 * z10 ≡ 1 [ZMOD ↑b]
      rw [← hdetγ]; exact (hz00b.mul hz11b).sub (hz01b.mul hz10b)
  set M : Matrix (Fin 2) (Fin 2) ℤ := !![z00, z01; z10, z11]
  have hM_det : (M.map (Int.castRingHom (ZMod (Nat.lcm a b)))).det = 1 := by
    simp only [det_fin_two, M, Matrix.map_apply, Int.coe_castRingHom]
    have h := intModEq_to_zmod hdet_lcm
    push_cast at h ⊢; exact_mod_cast h
  obtain ⟨β, hβ⟩ := SL2Reduction.SL2_reduction_surjective (Nat.lcm a b)
    ⟨M.map (Int.castRingHom (ZMod (Nat.lcm a b))), hM_det⟩
  have hβ_mat : (↑(SpecialLinearGroup.map (Int.castRingHom (ZMod (Nat.lcm a b))) β) :
      Matrix (Fin 2) (Fin 2) (ZMod (Nat.lcm a b))) =
      M.map (Int.castRingHom (ZMod (Nat.lcm a b))) := congr_arg Subtype.val hβ
  have hzM : ∀ i j : Fin 2, (M i j : ZMod a) = ((1 : SpecialLinearGroup (Fin 2) ℤ) i j : ZMod a) ∧
      (M i j : ZMod b) = (γ i j : ZMod b) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      exact ⟨intModEq_to_zmod ‹_›, intModEq_to_zmod ‹_›⟩
  have hβ_a : β ∈ CongruenceSubgroup.Gamma a := by
    rw [CongruenceSubgroup.Gamma_mem']; ext i j
    rw [crt_lift_reduces_mod M β hβ_mat (Nat.dvd_lcm_left a b) i j, (hzM i j).1]
    simp [Matrix.one_apply]
  have hβγ_b : β⁻¹ * γ ∈ CongruenceSubgroup.Gamma b := by
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv]
    have hβ_b : SpecialLinearGroup.map (Int.castRingHom (ZMod b)) β =
        SpecialLinearGroup.map (Int.castRingHom (ZMod b)) γ := by
      ext i j
      rw [crt_lift_reduces_mod M β hβ_mat (Nat.dvd_lcm_right a b) i j, (hzM i j).2]
      simp
    rw [hβ_b]; exact inv_mul_cancel _
  exact ⟨β, hβ_a, β⁻¹ * γ, hβγ_b, by group⟩

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
  · haveI : (Gamma a).Normal := Gamma_normal a
    haveI : NeZero (Nat.lcm a b) :=
      ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    intro γ hγ
    rw [Subgroup.mem_sup_of_normal_left]
    exact exists_Gamma_factor_of_mem_Gamma_gcd a b γ hγ
  · exact sup_le (Gamma_le_of_dvd (Nat.gcd_dvd_left a b))
      (Gamma_le_of_dvd (Nat.gcd_dvd_right a b))

/-- If `N ∣ (P · Q)_{10}`, `N ∣ P_{10}`, and `gcd(P_{11}, N) = 1`, then `N ∣ Q_{10}`.
    The product entry expands as `P_{10} Q_{00} + P_{11} Q_{10}`, so coprimality of
    `P_{11}` with `N` transfers the divisibility to `Q_{10}`. -/
private lemma dvd_apply_one_zero_of_dvd_mul (P Q : Matrix (Fin 2) (Fin 2) ℤ)
    (hPQ : (N : ℤ) ∣ (P * Q) 1 0) (hP10 : (N : ℤ) ∣ P 1 0)
    (hP11 : Int.gcd (P 1 1) N = 1) : (N : ℤ) ∣ Q 1 0 := by
  have key : (P * Q) 1 0 = P 1 0 * Q 0 0 + P 1 1 * Q 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [key] at hPQ
  have h2 : (N : ℤ) ∣ P 1 1 * Q 1 0 := by
    have h1 : (N : ℤ) ∣ P 1 0 * Q 0 0 := dvd_mul_of_dvd_left hP10 _
    have := Int.dvd_sub hPQ h1
    rwa [add_sub_cancel_left] at this
  rw [mul_comm] at h2
  exact (Int.isCoprime_iff_gcd_eq_one.mpr hP11).symm.dvd_of_dvd_mul_right h2

/-- For `τ` with `N ∣ τ_{10}` and `N ∣ (τ_{11} - 1)` (a `Γ(N)`-type condition) and
    `A` with `N ∣ A_{10}` and `gcd(A_{11}, N) = 1`, the product `C = τ · A` inherits
    both: `N ∣ C_{10}` and `gcd(C_{11}, N) = 1`. Used for the matrix `τ_N · A` in
    `doubleCoset_eq_of_Gamma0_coprimeDet`. -/
private lemma Gamma0_mul_apply_one_zero_and_gcd (τ A : Matrix (Fin 2) (Fin 2) ℤ)
    (hτ10 : (N : ℤ) ∣ τ 1 0) (hτ11 : (N : ℤ) ∣ (τ 1 1 - 1))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco2 : Int.gcd (A 1 1) N = 1) :
    (N : ℤ) ∣ (τ * A) 1 0 ∧ Int.gcd ((τ * A) 1 1) N = 1 := by
  refine ⟨?_, ?_⟩
  · have : (τ * A) 1 0 = τ 1 0 * A 0 0 + τ 1 1 * A 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_right hAN _)
  · rw [← Int.isCoprime_iff_gcd_eq_one]
    have hmod : (N : ℤ) ∣ ((τ * A) 1 1 - A 1 1) := by
      have : (τ * A) 1 1 - A 1 1 = τ 1 0 * A 0 1 + (τ 1 1 - 1) * A 1 1 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_left hτ11 _)
    obtain ⟨k, hk⟩ := hmod
    rw [show (τ * A) 1 1 = A 1 1 + k * ↑N from by linarith]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hAco2).add_mul_right_left k

/-- The rational matrix of `mapGL τ · g · mapGL δ` is the integer matrix product
    `τ · A · δ` cast to `ℚ`, where `↑g = A.map (Int.cast)`. Lets one read off the
    integer witness of a `Γ₀(N)`-translated double-coset element. -/
private lemma mapGL_mul_coe_eq_intMatrix (τ δ : SpecialLinearGroup (Fin 2) ℤ)
    (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    (↑(mapGL ℚ τ * g * mapGL ℚ δ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((τ : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ) := by
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hA]
  ext i j; simp [Matrix.mul_apply, Matrix.map_apply]

open CongruenceSubgroup in
/-- The forward (`⊆`) direction of `doubleCoset_eq_of_Gamma0_coprimeDet`: an
    `SL₂(ℤ)`-double-coset element `σ₁ · α · σ₂` that lies in `Δ₀(N)` is already a
    `Γ₀(N)`-double-coset element. Factor `σ₁ = τ_N · τ_a` (Shimura 3.28) with
    `τ_N ∈ Γ(N)` and `τ_a ∈ Γ(det α)`; the conjugation `Γ(det α) ⊆ αΓα⁻¹`
    rewrites the element as `τ_N · α · γ₂'`, and coprimality of `τ_N · A` forces
    `γ₂' ∈ Γ₀(N)`. -/
private lemma mem_Gamma0_doubleCoset_of_mem_Delta0
    (α : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco2 : Int.gcd (A 1 1) N = 1)
    (hAdet_ne : A.det ≠ 0) (hdet_coprime : Int.gcd A.det N = 1)
    (σ₁ σ₂ : SpecialLinearGroup (Fin 2) ℤ)
    (hx_delta : mapGL ℚ σ₁ * α * mapGL ℚ σ₂ ∈ Delta0_submonoid N) :
    mapGL ℚ σ₁ * α * mapGL ℚ σ₂ ∈ DoubleCoset.doubleCoset α
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  haveI : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet_ne⟩
  haveI : NeZero (Nat.gcd A.det.natAbs N) :=
    ⟨by rw [show Nat.gcd A.det.natAbs N = Int.gcd A.det N from rfl, hdet_coprime]
        exact one_ne_zero⟩
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
  have hτ_N_Gamma0 : τ_N ∈ Gamma0 N := GammaN_le_Gamma0 N hτ_N
  have hτ10 : (N : ℤ) ∣ (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rwa [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ_N_Gamma0
  have hτ11 : (N : ℤ) ∣ ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
    rw [Gamma_mem] at hτ_N
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; simp [hτ_N.2.2.2])
  have hτ_ker : τ_a ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker := by
    rw [MonoidHom.mem_ker]; rwa [Gamma_mem'] at hτ_a
  obtain ⟨h_sl, hh_sl⟩ := conj_ker_mem_SLnZ 2 α A hA hAdet_ne τ_a hτ_ker
  set γ₂' := h_sl * σ₂
  have hx_eq' : mapGL ℚ σ₁ * α * mapGL ℚ σ₂ = mapGL ℚ τ_N * α * mapGL ℚ γ₂' := by
    rw [hσ₁_eq.symm, map_mul, map_mul, mul_assoc, mul_assoc, mul_assoc]
    congr 1; rw [← mul_assoc, show mapGL ℚ τ_a * α = α * mapGL ℚ h_sl from by rw [hh_sl]; group,
      mul_assoc]
  obtain ⟨hCN, hCco2⟩ := Gamma0_mul_apply_one_zero_and_gcd N
    (τ_N : Matrix (Fin 2) (Fin 2) ℤ) A hτ10 hτ11 hAN hAco2
  have hγ₂'_mem : γ₂' ∈ Gamma0 N := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine dvd_apply_one_zero_of_dvd_mul N _ (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) ?_ hCN hCco2
    obtain ⟨_, _, B, hB, hBN, _⟩ := hx_delta
    have hB_eq : B = (τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) :=
      Matrix.map_injective (Int.cast_injective)
        (hB.symm.trans (hx_eq' ▸ mapGL_mul_coe_eq_intMatrix τ_N γ₂' α A hA))
    rw [← hB_eq]; exact hBN
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨mapGL ℚ τ_N, Subgroup.mem_map_of_mem _ hτ_N_Gamma0,
    mapGL ℚ γ₂', Subgroup.mem_map_of_mem _ hγ₂'_mem, hx_eq'⟩

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
  · intro ⟨hx_dc, hx_delta⟩
    rw [DoubleCoset.mem_doubleCoset] at hx_dc
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx_dc
    obtain ⟨σ₁, rfl⟩ := hγ₁; obtain ⟨σ₂, rfl⟩ := hγ₂
    rw [SetLike.mem_coe] at hx_delta
    rw [hx_eq] at hx_delta ⊢
    exact mem_Gamma0_doubleCoset_of_mem_Delta0 N α A hA hAN hAco2
      (ne_of_gt hAdet_pos) hdet_coprime σ₁ σ₂ hx_delta
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

end HeckeRing.GLn
