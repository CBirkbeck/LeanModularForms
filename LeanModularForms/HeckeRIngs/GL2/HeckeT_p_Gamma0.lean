/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_GLpair
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0

/-!
# The Hecke double coset `D_p` in `𝕋(Γ₀(N))`

Defines the Γ₀(N)-level double coset `Γ₀(N) · diag(1,p) · Γ₀(N)` and related
infrastructure. This is the basis element in the Hecke algebra `𝕋(Gamma0_pair N) ℤ`
whose image under `heckeRingHom_Gamma0 N k` is the Hecke operator `T_p` at
level Γ₀(N).

## Main definitions

* `D_p_Gamma0 N p hp` — the double coset `Γ₀(N) · diag(1,p) · Γ₀(N)`.
* `diag_1p_delta_Gamma0 N p hp` — `diag(1,p)` as an element of `Δ₀(N)`.
* `T_p_upper_mem_Delta0` — the upper-triangular reps live in `Δ₀(N)`.
* `T_p_lower_mem_Delta0` — the lower-triangular rep lives in `Δ₀(N)` when
  `gcd(p,N) = 1`.

## Main results

* `HeckeCoset_deg_D_p_Gamma0` — the double coset has exactly `p + 1` left cosets.
* `T_p_upper_mem_D_p_Gamma0` — `T_p_upper(b) ∈ D_p_Gamma0` for all `b`.
* `T_p_lower_mem_D_p_Gamma0` — `T_p_lower ∈ D_p_Gamma0` for `gcd(p, N) = 1`.

## References

* Shimura, §3.4, Theorem 3.35.
* Diamond–Shurman, §5.2, Proposition 5.2.1.
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

/-- `diag(1,p)` lies in `Δ₀(N)` for any `N` and `p > 0`. -/
lemma diag_1p_mem_Delta0 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    diagMat 2 ![1, p] ∈ Delta0_submonoid N := by
  have ha : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := fun i ↦ by fin_cases i <;> simp [hp]
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal (fun i ↦ ((![1, p] i : ℕ) : ℤ))
  have hcoe : (↑(diagMat 2 ![1, p]) : Matrix _ _ ℚ) =
      Matrix.diagonal (fun i ↦ ((![1, p] i : ℕ) : ℚ)) := by
    unfold diagMat; rw [dif_pos ha]; rfl
  have hA_eq : (↑(diagMat 2 ![1, p]) : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    rw [hcoe]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.diagonal, Matrix.map_apply, Int.cast_natCast]
  refine ⟨⟨A, hA_eq⟩, by rw [hcoe, Matrix.det_diagonal]; simp; exact_mod_cast hp,
    A, hA_eq, by simp [A, Matrix.diagonal], by simp [A, Matrix.diagonal]⟩

/-- `diag(1,p)` as an element of `(Gamma0_pair N).Δ`. -/
noncomputable def diag_1p_delta_Gamma0 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    (Gamma0_pair N).Δ :=
  ⟨diagMat 2 ![1, p], diag_1p_mem_Delta0 N p hp⟩

/-- The double coset `Γ₀(N) · diag(1,p) · Γ₀(N)` in `Gamma0_pair N`.
This is the Hecke double coset representing the operator `T_p` at level `Γ₀(N)`. -/
noncomputable def D_p_Gamma0 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    HeckeRing.HeckeCoset (Gamma0_pair N) :=
  ⟦diag_1p_delta_Gamma0 N p hp⟧

/-- Membership of `T_p_upper(b)` in `Δ₀(N)`.
The top-left entry is `1`, so the `gcd` condition is automatic; the lower-left
entry is `0`, so the divisibility condition is automatic. -/
lemma T_p_upper_mem_Delta0 (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (T_p_upper p hp b : GL (Fin 2) ℚ) ∈ Delta0_submonoid N := by
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![1, (b : ℤ); 0, (p : ℤ)]
  have hA_eq : (↑(T_p_upper p hp b) : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, A, Matrix.map_apply]
  exact ⟨⟨A, hA_eq⟩, by rw [T_p_upper_det]; exact_mod_cast hp,
    A, hA_eq, by simp [A], by simp [A]⟩

/-- Membership of `T_p_lower p` in `Δ₀(N)` requires `gcd(p, N) = 1` because the
top-left entry is `p`. -/
lemma T_p_lower_mem_Delta0 (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    (T_p_lower p hp : GL (Fin 2) ℚ) ∈ Delta0_submonoid N := by
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), 0; 0, 1]
  have hA_eq : (↑(T_p_lower p hp) : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, A, Matrix.map_apply]
  exact ⟨⟨A, hA_eq⟩, by rw [T_p_lower_det]; exact_mod_cast hp,
    A, hA_eq, by simp [A], by simp only [A]; exact_mod_cast hpN⟩



/-- The Γ₀(N)-double coset degree of `diag(1,p)` is `p + 1` for `p` prime
coprime to `N`: the `decompQuot` has exactly `p + 1` elements. -/
lemma HeckeCoset_deg_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    Nat.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeRing.HeckeCoset.rep (D_p_Gamma0 N p hp.pos))) = p + 1 := by
  have h_deg := HeckeCoset_deg_Gamma0_one_ppow N p hp hpN 1 (by lia)
  have hpp : (![1, p] : Fin 2 → ℕ) = ![1, p^1] := by ext i; fin_cases i <;> simp
  have h_eq : (D_p_Gamma0 N p hp.pos : HeckeRing.HeckeCoset (Gamma0_pair N)) =
      T_diag_Gamma0 N (![1, p^1])
        (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | simp; exact hp.pos)
        (by simp) := by
    apply (HeckeRing.HeckeCoset.eq_iff _ _).mpr
    show DoubleCoset.doubleCoset (diagMat 2 (![1, p] : Fin 2 → ℕ) : GL _ ℚ) _ _ =
      DoubleCoset.doubleCoset (diagMat 2 (![1, p^1] : Fin 2 → ℕ) : GL _ ℚ) _ _
    rw [hpp]
  rw [h_eq, Nat.card_eq_fintype_card]
  unfold HeckeRing.HeckeCoset_deg at h_deg
  have h_nat : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
      (HeckeRing.HeckeCoset.rep (T_diag_Gamma0 N (![1, p^1])
        (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | simp; exact hp.pos)
        (by simp)))) = p^(1-1) * (p + 1) := by exact_mod_cast h_deg
  rw [h_nat]; simp

private lemma mem_D_p_Gamma0_of_factor_through_diag (N : ℕ) [NeZero N] (p : ℕ)
    (hp : 0 < p) (g s t : GL (Fin 2) ℚ) (hs : s ∈ (Gamma0_pair N).H)
    (ht : t ∈ (Gamma0_pair N).H)
    (hfact : g = s * (diag_1p_delta_Gamma0 N p hp : GL (Fin 2) ℚ) * t) :
    g ∈ HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp) := by
  rw [HeckeRing.HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  have hrep := HeckeRing.HeckeCoset.rep_mem (D_p_Gamma0 N p hp)
  rw [D_p_Gamma0, HeckeRing.HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  refine ⟨s * a⁻¹, (Gamma0_pair N).H.mul_mem hs ((Gamma0_pair N).H.inv_mem ha),
    c⁻¹ * t, (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem hc) ht, ?_⟩
  rw [hfact, show (diag_1p_delta_Gamma0 N p hp : GL (Fin 2) ℚ) =
    a⁻¹ * (HeckeRing.HeckeCoset.rep (D_p_Gamma0 N p hp) : GL (Fin 2) ℚ) * c⁻¹ by
      unfold D_p_Gamma0; rw [habc]; group]
  group

private lemma bezout_int_of_coprime (p N : ℕ) (hpN : Nat.Coprime p N) :
    ∃ u v : ℤ, u * (p : ℤ) - v * (N : ℤ) = 1 := by
  refine ⟨Int.gcdA (p : ℤ) (N : ℤ), -Int.gcdB (p : ℤ) (N : ℤ), ?_⟩
  have h := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
  rw [show Int.gcd (p : ℤ) (N : ℤ) = 1 from by rw [Int.gcd_natCast_natCast]; exact hpN] at h
  push_cast at h; linarith

private lemma T_p_lower_factor_through_diag_1p (N : ℕ) [NeZero N] (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    ∃ (s : GL (Fin 2) ℚ) (_ : s ∈ (Gamma0_pair N).H) (t : GL (Fin 2) ℚ)
      (_ : t ∈ (Gamma0_pair N).H),
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
        s * (diag_1p_delta_Gamma0 N p hp.pos : GL (Fin 2) ℚ) * t := by
  obtain ⟨u, v, h_bezout⟩ := bezout_int_of_coprime p N hpN
  set σ : SL(2, ℤ) := ⟨!![(p : ℤ), v; (N : ℤ), u],
    by rw [det_fin_two]; simp; linarith [h_bezout]⟩
  set τ : SL(2, ℤ) := ⟨!![u * p, -v; -(N : ℤ), 1],
    by rw [det_fin_two]; simp; linarith [h_bezout]⟩
  refine ⟨mapGL ℚ σ,
    Subgroup.mem_map_of_mem _ (by rw [CongruenceSubgroup.Gamma0_mem]; simp [σ]),
    mapGL ℚ τ,
    Subgroup.mem_map_of_mem _ (by rw [CongruenceSubgroup.Gamma0_mem]; simp [τ]), ?_⟩
  have h_bezout_Q : (u : ℚ) * (p : ℚ) - (v : ℚ) * (N : ℚ) = 1 := by exact_mod_cast h_bezout
  apply Units.ext; ext i j
  have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k ↦ by
    fin_cases k <;> simp [hp.pos]
  show (T_p_lower p hp.pos : GL (Fin 2) ℚ).val i j =
    (mapGL ℚ σ * (diagMat 2 ![1, p] : GL (Fin 2) ℚ) * mapGL ℚ τ).val i j
  simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, σ, τ, mapGL_coe_matrix,
      algebraMap_int_eq]
  · linear_combination -(p : ℚ) * h_bezout_Q
  · ring
  · ring
  · linear_combination -h_bezout_Q

/-- Membership of `T_p_upper(b)` in the Γ₀(N)-double coset `D_p_Gamma0`, via the
factorization `T_p_upper(b) = diag(1,p) · σ_b` with `σ_b = [[1,b],[0,1]] ∈ Γ₀(N)`. -/
lemma T_p_upper_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∈
      HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  set σ_b : SL(2, ℤ) := ⟨!![1, (b : ℤ); 0, 1], by simp [det_fin_two]⟩
  have hσ_Gamma0 : σ_b ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((!![1, (b : ℤ); 0, 1] : Matrix _ _ ℤ) 1 0 : ZMod N) = 0
    simp
  refine mem_D_p_Gamma0_of_factor_through_diag N p hp.pos _ 1 (mapGL ℚ σ_b)
    (one_mem _) (Subgroup.mem_map_of_mem _ hσ_Gamma0) ?_
  apply Units.ext; ext i j
  have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k ↦ by
    fin_cases k <;> simp [hp.pos]
  show (T_p_upper p hp.pos b : GL (Fin 2) ℚ).val i j =
    (1 * (diagMat 2 ![1, p] : GL (Fin 2) ℚ) * (mapGL ℚ σ_b)).val i j
  simp only [one_mul, diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, σ_b, mapGL_coe_matrix,
      algebraMap_int_eq]

/-- Membership of `T_p_lower` in the Γ₀(N)-double coset `D_p_Gamma0`, via the Bezout
factorization `T_p_lower = σ · diag(1,p) · τ` with `σ, τ ∈ Γ₀(N)`. -/
lemma T_p_lower_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∈
      HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  obtain ⟨s, hs, t, ht, hfact⟩ := T_p_lower_factor_through_diag_1p N p hp hpN
  exact mem_D_p_Gamma0_of_factor_through_diag N p hp.pos _ s t hs ht hfact

/-- Inclusion `(Gamma0_pair N).H ≤ (GL_pair 2).H = SLnZ_subgroup 2`. Γ₀(N) is the
image of the inclusion `Γ₀(N) ↪ SL₂(ℤ)` under `mapGL`. -/
lemma Gamma0_pair_H_le_GL_pair_H (N : ℕ) [NeZero N] :
    (HeckeRing.GLn.Gamma0_pair N).H ≤ (GL_pair 2).H := fun _ hg ↦
  let ⟨s, _, hs⟩ := Subgroup.mem_map.mp hg
  ⟨s, hs⟩

end HeckeRing.GL2
