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

This is step 1 of the refactor to derive Γ₁(N) Hecke operator commutativity
from commutativity of the Hecke ring `𝕋(Γ₀(N))` via character decomposition.

## Main definitions

* `D_p_Gamma0 N p hp` — the double coset `Γ₀(N) · diag(1,p) · Γ₀(N)`.
* `diag_1p_delta_Gamma0 N p hp` — `diag(1,p)` as an element of `Δ₀(N)`.
* `T_p_upper_mem_Delta0` — the upper-triangular reps live in `Δ₀(N)`.
* `T_p_lower_mem_Delta0` — the lower-triangular rep lives in `Δ₀(N)` when
  `gcd(p,N) = 1`.

## Main results (step 2)

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

/-! ### `diag(1,p) ∈ Δ₀(N)` and the double coset -/

/-- `diag(1,p)` lies in `Δ₀(N)` for any `N` and `p > 0`. -/
lemma diag_1p_mem_Delta0 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    diagMat 2 ![1, p] ∈ Delta0_submonoid N := by
  have ha : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := fun i => by fin_cases i <;> simp [hp]
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal (fun i => ((![1, p] i : ℕ) : ℤ))
  have hcoe : (↑(diagMat 2 ![1, p]) : Matrix _ _ ℚ) =
      Matrix.diagonal (fun i => ((![1, p] i : ℕ) : ℚ)) := by
    unfold diagMat; rw [dif_pos ha]; rfl
  have hA_eq : (↑(diagMat 2 ![1, p]) : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    rw [hcoe]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.diagonal, Matrix.map_apply, Int.cast_natCast]
  refine ⟨⟨A, hA_eq⟩, by rw [hcoe, Matrix.det_diagonal]; simp; exact_mod_cast hp,
    A, hA_eq, ?_, ?_⟩
  · -- N ∣ A 1 0: off-diagonal entry of diagonal matrix is 0
    simp [A, Matrix.diagonal]
  · -- Int.gcd (A 0 0) N = 1: top-left entry is 1
    simp [A, Matrix.diagonal]

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
  refine ⟨⟨A, hA_eq⟩, ?_, A, hA_eq, ?_, ?_⟩
  · rw [T_p_upper_det]; exact_mod_cast hp
  · simp [A]
  · simp [A]

/-- Membership of `T_p_lower p` in `Δ₀(N)` requires `gcd(p, N) = 1` because the
top-left entry is `p`. -/
lemma T_p_lower_mem_Delta0 (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    (T_p_lower p hp : GL (Fin 2) ℚ) ∈ Delta0_submonoid N := by
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), 0; 0, 1]
  have hA_eq : (↑(T_p_lower p hp) : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, A, Matrix.map_apply]
  refine ⟨⟨A, hA_eq⟩, ?_, A, hA_eq, ?_, ?_⟩
  · rw [T_p_lower_det]; exact_mod_cast hp
  · simp [A]
  · -- Int.gcd p N = 1 from Nat.Coprime p N
    simp only [A]
    exact_mod_cast hpN

/-- `T_p_upper(b)` as an element of `(Gamma0_pair N).Δ`. -/
noncomputable def T_p_upper_delta_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (Gamma0_pair N).Δ :=
  ⟨T_p_upper p hp b, T_p_upper_mem_Delta0 N p hp b⟩

/-- `T_p_lower p` as an element of `(Gamma0_pair N).Δ` when `gcd(p,N) = 1`. -/
noncomputable def T_p_lower_delta_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p)
    (hpN : Nat.Coprime p N) : (Gamma0_pair N).Δ :=
  ⟨T_p_lower p hp, T_p_lower_mem_Delta0 N p hp hpN⟩

/-! ### Degree of `D_p_Gamma0` and coset representatives

For `p` prime coprime to `N`, the double coset `Γ₀(N) · diag(1,p) · Γ₀(N)` decomposes
into exactly `p + 1` left `Γ₀(N)`-cosets. The standard representatives are the
classical `T_p` coset reps: `T_p_upper(b) = [[1,b],[0,p]]` for `b = 0, …, p-1` and
`T_p_lower = [[p,0],[0,1]]`. -/

/-- The cosets `T_diag_Gamma0 N ![1, p]` and `D_p_Gamma0 N p` agree because they are
represented by the same underlying matrix `diag(1, p)`. -/
lemma D_p_Gamma0_eq_T_diag (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p)
    (_hpN : Nat.Coprime p N) :
    D_p_Gamma0 N p hp =
      T_diag_Gamma0 N (![1, p]) (fun i => by fin_cases i <;> simp [hp])
        (by show Int.gcd ((![1, p] : Fin 2 → ℕ) 0 : ℤ) N = 1; simp) := by
  simp only [D_p_Gamma0, diag_1p_delta_Gamma0, T_diag_Gamma0]

/-- **Phase 1**: The Γ₀(N)-double coset degree of `diag(1,p)` is `p + 1` for `p` prime
coprime to `N`. Equivalently, the `decompQuot` has exactly `p + 1` elements. -/
lemma HeckeCoset_deg_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    Nat.card (HeckeRing.decompQuot (Gamma0_pair N)
        (HeckeRing.HeckeCoset.rep (D_p_Gamma0 N p hp.pos))) = p + 1 := by
  -- Use HeckeCoset_deg_Gamma0_one_ppow at k = 1.
  have h_deg := HeckeCoset_deg_Gamma0_one_ppow N p hp hpN 1 (by omega)
  -- Key: the underlying Δ-element of `D_p_Gamma0` coincides with the one in
  -- `T_diag_Gamma0 N ![1, p^1]` up to proof irrelevance, because `![1, p] = ![1, p^1]`.
  have hpp : (![1, p] : Fin 2 → ℕ) = ![1, p^1] := by
    ext i; fin_cases i <;> simp
  -- The two HeckeCosets are equal since their underlying GL elements coincide.
  have h_eq : (D_p_Gamma0 N p hp.pos : HeckeRing.HeckeCoset (Gamma0_pair N)) =
      T_diag_Gamma0 N (![1, p^1])
        (fun i => by
          fin_cases i <;> first | exact Nat.one_pos | simp; exact hp.pos)
        (by simp [Int.gcd_one_left]) := by
    apply (HeckeRing.HeckeCoset.eq_iff _ _).mpr
    show DoubleCoset.doubleCoset (diagMat 2 (![1, p] : Fin 2 → ℕ) : GL _ ℚ) _ _ =
      DoubleCoset.doubleCoset (diagMat 2 (![1, p^1] : Fin 2 → ℕ) : GL _ ℚ) _ _
    rw [hpp]
  -- Rewrite and extract the cardinality.
  rw [h_eq]
  -- h_deg : HeckeCoset_deg (Gamma0_pair N) (T_diag_Gamma0 ...) = ((p^(1-1) * (p + 1) : ℕ) : ℤ)
  -- HeckeCoset_deg unfolds to (Fintype.card ... : ℤ)
  unfold HeckeRing.HeckeCoset_deg at h_deg
  rw [Nat.card_eq_fintype_card]
  have h_nat : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N)
      (HeckeRing.HeckeCoset.rep (T_diag_Gamma0 N (![1, p^1])
        (fun i => by
          fin_cases i <;> first | exact Nat.one_pos | simp; exact hp.pos)
        (by simp [Int.gcd_one_left])))) = p^(1-1) * (p + 1) := by
    exact_mod_cast h_deg
  rw [h_nat]; simp

/-! ### Phase 2: membership of `T_p_upper(b)` and `T_p_lower` in `D_p_Gamma0`

Both `T_p_upper(b) = [[1,b],[0,p]]` and `T_p_lower = [[p,0],[0,1]]` lie in the
Γ₀(N)-double coset of `diag(1,p)`. The upper-triangular case uses the factorization
`T_p_upper(b) = diag(1,p) · [[1,b],[0,1]]`, where `[[1,b],[0,1]] ∈ Γ₀(N)` since its
lower-left entry is `0`. The lower-triangular case uses Bezout: for `u·p - v·N = 1`,
`T_p_lower = [[p, v], [N, u]] · diag(1,p) · [[u·p, -v], [-N, 1]]` with both outer
factors in Γ₀(N) (lower-left entries `N` and `-N` respectively). -/

/-- **Membership of `T_p_upper(b)` in the Γ₀(N)-double coset `D_p_Gamma0`**.
The factorization `T_p_upper(b) = diag(1,p) · σ_b` with `σ_b = [[1,b],[0,1]]` shows
that `T_p_upper(b)` is in the right Γ₀(N)-coset of `diag(1,p)`. Combined with the
representative absorption for the rep of `D_p_Gamma0`, this gives double-coset
membership. -/
lemma T_p_upper_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∈
      HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  rw [HeckeRing.HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  -- The rep of D_p_Gamma0 is in the double coset of diag(1,p)
  have hrep := HeckeRing.HeckeCoset.rep_mem (D_p_Gamma0 N p hp.pos)
  rw [D_p_Gamma0, HeckeRing.HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  -- Build σ_b = [[1, b], [0, 1]] ∈ SL₂(ℤ) ∩ Γ₀(N) (lower-left is 0)
  have hσ_det : (!![1, (b : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set σ_b : SL(2, ℤ) := ⟨!![1, (b : ℤ); 0, 1], hσ_det⟩
  have hσ_Gamma0 : σ_b ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((!![1, (b : ℤ); 0, 1] : Matrix _ _ ℤ) 1 0 : ZMod N) = 0
    simp
  have hσ_mem : mapGL ℚ σ_b ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map_of_mem _ hσ_Gamma0
  -- T_p_upper(b) = diag(1,p) * σ_b
  have hfact : (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
      (diag_1p_delta_Gamma0 N p hp.pos : GL (Fin 2) ℚ) * (mapGL ℚ σ_b) := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
      fin_cases k <;> simp [hp.pos]
    show (T_p_upper p hp.pos b : GL (Fin 2) ℚ).val i j =
      ((diagMat 2 ![1, p] : GL (Fin 2) ℚ) * (mapGL ℚ σ_b)).val i j
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, σ_b, mapGL_coe_matrix,
        algebraMap_int_eq]
  -- diag(1,p) = a⁻¹ * rep * c⁻¹, from habc : rep = a * diag(1,p) * c
  have hdiag_eq : (diag_1p_delta_Gamma0 N p hp.pos : GL (Fin 2) ℚ) =
      a⁻¹ * (HeckeRing.HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL (Fin 2) ℚ) * c⁻¹ := by
    unfold D_p_Gamma0; rw [habc]; group
  -- T_p_upper(b) = a⁻¹ * rep * (c⁻¹ * σ_b) with a⁻¹ ∈ H and c⁻¹ * σ_b ∈ H
  refine ⟨a⁻¹, (Gamma0_pair N).H.inv_mem ha, c⁻¹ * mapGL ℚ σ_b,
    (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem hc) hσ_mem, ?_⟩
  rw [hfact, hdiag_eq, mul_assoc, mul_assoc]

/-- **Membership of `T_p_lower` in the Γ₀(N)-double coset `D_p_Gamma0`**.
Uses the Bezout factorization `T_p_lower = σ · diag(1,p) · τ` where for `u,v`
satisfying `u·p - v·N = 1` (Bezout, since `gcd(p,N) = 1`),
`σ = [[p,v],[N,u]]` and `τ = [[up,-v],[-N,1]]` are both in Γ₀(N). -/
lemma T_p_lower_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∈
      HeckeRing.HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  rw [HeckeRing.HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  -- rep ∈ D_p_Gamma0, so rep = a * diag(1,p) * c with a, c ∈ H
  have hrep := HeckeRing.HeckeCoset.rep_mem (D_p_Gamma0 N p hp.pos)
  rw [D_p_Gamma0, HeckeRing.HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  -- Bezout: find u, v ∈ ℤ with u * p - v * N = 1.
  -- gcd_eq_gcd_ab: Int.gcd p N = p * p.gcdA N + N * p.gcdB N
  -- With Int.gcd p N = 1 (from hpN), letting u := p.gcdA N and v := -p.gcdB N,
  -- we get p * u + N * (-v) = 1, i.e. u * p - v * N = 1.
  set u : ℤ := Int.gcdA (p : ℤ) (N : ℤ) with hu_def
  set v : ℤ := -Int.gcdB (p : ℤ) (N : ℤ) with hv_def
  have h_gcd : Int.gcd (p : ℤ) (N : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hpN
  have h_bezout : u * (p : ℤ) - v * (N : ℤ) = 1 := by
    have h := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
    rw [h_gcd] at h
    -- h : (↑(1 : ℕ) : ℤ) = p * gcdA + N * gcdB
    push_cast at h
    simp only [hu_def, hv_def]
    linarith
  -- σ = [[p, v], [N, u]] ∈ Γ₀(N), det = u*p - v*N = 1
  have hσ_det : (!![(p : ℤ), v; (N : ℤ), u] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [det_fin_two]; simp; linarith [h_bezout]
  set σ : SL(2, ℤ) := ⟨!![(p : ℤ), v; (N : ℤ), u], hσ_det⟩
  have hσ_Gamma0 : σ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((!![(p : ℤ), v; (N : ℤ), u] : Matrix _ _ ℤ) 1 0 : ZMod N) = 0
    simp
  have hσ_mem : mapGL ℚ σ ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map_of_mem _ hσ_Gamma0
  -- τ = [[u*p, -v], [-N, 1]] ∈ Γ₀(N), det = u*p*1 - (-v)*(-N) = u*p - v*N = 1
  have hτ_det : (!![u * p, -v; -(N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [det_fin_two]; simp; linarith [h_bezout]
  set τ : SL(2, ℤ) := ⟨!![u * p, -v; -(N : ℤ), 1], hτ_det⟩
  have hτ_Gamma0 : τ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((!![u * p, -v; -(N : ℤ), 1] : Matrix _ _ ℤ) 1 0 : ZMod N) = 0
    simp
  have hτ_mem : mapGL ℚ τ ∈ (Gamma0_pair N).H :=
    Subgroup.mem_map_of_mem _ hτ_Gamma0
  -- T_p_lower = σ * diag(1,p) * τ
  -- Bezout over ℚ: u*p - v*N = 1 cast to ℚ
  have h_bezout_Q : (u : ℚ) * (p : ℚ) - (v : ℚ) * (N : ℚ) = 1 := by
    have := h_bezout; exact_mod_cast this
  have hfact : (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      mapGL ℚ σ * (diag_1p_delta_Gamma0 N p hp.pos : GL (Fin 2) ℚ) * mapGL ℚ τ := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
      fin_cases k <;> simp [hp.pos]
    show (T_p_lower p hp.pos : GL (Fin 2) ℚ).val i j =
      (mapGL ℚ σ * (diagMat 2 ![1, p] : GL (Fin 2) ℚ) * mapGL ℚ τ).val i j
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, σ, τ, mapGL_coe_matrix,
        algebraMap_int_eq]
    · -- Entry (0,0): simp reduces to p + pvN - p²u = 0, i.e. p*(pu - vN - 1) = 0.
      linear_combination -(p : ℚ) * h_bezout_Q
    · -- Entry (0,1): simp-goal is identically 0 = 0 after normalization.
      ring
    · -- Entry (1,0)
      ring
    · -- Entry (1,1)
      linear_combination -h_bezout_Q
  -- diag(1,p) = a⁻¹ * rep * c⁻¹
  have hdiag_eq : (diag_1p_delta_Gamma0 N p hp.pos : GL (Fin 2) ℚ) =
      a⁻¹ * (HeckeRing.HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL (Fin 2) ℚ) * c⁻¹ := by
    unfold D_p_Gamma0; rw [habc]; group
  -- T_p_lower = (mapGL σ * a⁻¹) * rep * (c⁻¹ * mapGL τ) with both outer factors in H
  refine ⟨mapGL ℚ σ * a⁻¹,
    (Gamma0_pair N).H.mul_mem hσ_mem ((Gamma0_pair N).H.inv_mem ha),
    c⁻¹ * mapGL ℚ τ,
    (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem hc) hτ_mem, ?_⟩
  rw [hfact, hdiag_eq]; group

/-! ### Phase 3: distinctness of the `p+1` left `Γ₀(N)`-cosets

For distinct `b₁, b₂ ∈ [0, p)` and `p` prime, the representatives
`T_p_upper(b₁), T_p_upper(b₂), T_p_lower(p)` give distinct left `Γ₀(N)`-cosets.
The test is: `Γ₀(N) · A = Γ₀(N) · B  ⟺  A · B⁻¹ ∈ Γ₀(N).H`. We show
`T_p_upper(b₁) · T_p_upper(b₂)⁻¹ = [[1, (b₁ - b₂)/p], [0, 1]]` has a
non-integer `(0,1)`-entry, and `T_p_upper(b) · T_p_lower(p)⁻¹ = [[1/p, b], [0, p]]`
has a non-integer `(0,0)`-entry. Since `(Gamma0_pair N).H` consists of images of
`SL₂(ℤ)` matrices (integer entries), such matrices cannot lie in it. -/

/-- Elements of `(Gamma0_pair N).H` come from `SL₂(ℤ)` via `mapGL` and
therefore have integer entries. -/
private lemma Gamma0_pair_H_entry_is_int {N : ℕ} [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ (Gamma0_pair N).H) (i j : Fin 2) : ∃ n : ℤ, g.val i j = (n : ℚ) := by
  obtain ⟨s, _, hs⟩ := Subgroup.mem_map.mp hg
  exact ⟨s.val i j, by rw [← hs]; simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

set_option maxHeartbeats 1600000 in
/-- `T_p_upper(b₁) · T_p_upper(b₂)⁻¹ = [[1, (b₁ - b₂)/p], [0, 1]]` as `GL₂(ℚ)`. -/
private lemma T_p_upper_mul_upper_inv_eq (p : ℕ) (hp : Nat.Prime p) (b₁ b₂ : ℕ) :
    (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ) *
      (T_p_upper p hp.pos b₂ : GL (Fin 2) ℚ)⁻¹ =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(1 : ℚ), ((b₁ : ℤ) - (b₂ : ℤ) : ℤ) / (p : ℚ); 0, 1])
      (by simp [det_fin_two]) := by
  rw [mul_inv_eq_iff_eq_mul]; apply Units.ext; ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  fin_cases i <;> fin_cases j <;>
    simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, sub_div] <;>
    (try ring) <;> field_simp <;> ring

set_option maxHeartbeats 1600000 in
/-- `T_p_upper(b) · T_p_lower(p)⁻¹ = [[1/p, b], [0, p]]` as `GL₂(ℚ)`. -/
private lemma T_p_upper_mul_lower_inv_eq (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) *
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)⁻¹ =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(1 / (p : ℚ)), (b : ℚ); 0, (p : ℚ)])
      (by norm_num [det_fin_two]; exact hp.ne_zero) := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [mul_inv_eq_iff_eq_mul]; apply Units.ext; ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [T_p_upper, T_p_lower, GeneralLinearGroup.mkOfDetNeZero] <;>
    (try ring) <;> field_simp

set_option maxHeartbeats 1600000 in
/-- **Phase 3 (distinctness of upper reps)**: For distinct `b₁, b₂ < p`, the
representatives `T_p_upper(b₁)` and `T_p_upper(b₂)` lie in distinct left
`Γ₀(N)`-cosets. Equivalently, `T_p_upper(b₁) ≠ γ * T_p_upper(b₂)` for any
`γ ∈ (Gamma0_pair N).H`.

The proof: `T_p_upper(b₁) · T_p_upper(b₂)⁻¹ = [[1, (b₁-b₂)/p], [0, 1]]`. If
this equalled `γ`, the `(0,1)`-entry `(b₁-b₂)/p` would be an integer. But for
`b₁ ≠ b₂` with `|b₁-b₂| < p` and `p` prime, this is non-integer. -/
lemma T_p_upper_distinct_cosets_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (b₁ b₂ : ℕ) (hb₁ : b₁ < p) (hb₂ : b₂ < p) (hne : b₁ ≠ b₂) :
    ∀ γ ∈ (Gamma0_pair N).H,
      (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ) ≠ γ * T_p_upper p hp.pos b₂ := by
  intro γ hγ heq
  -- From heq: γ = T_p_upper(b₁) * T_p_upper(b₂)⁻¹
  have hγ_eq : γ = (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ) *
      (T_p_upper p hp.pos b₂ : GL (Fin 2) ℚ)⁻¹ := by
    rw [heq]; group
  rw [hγ_eq, T_p_upper_mul_upper_inv_eq p hp b₁ b₂] at hγ
  obtain ⟨n, hn⟩ := Gamma0_pair_H_entry_is_int _ hγ 0 1
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_rat : ((b₁ : ℤ) - (b₂ : ℤ) : ℚ) = (n : ℚ) * (p : ℚ) := by
    have := hn; field_simp at this ⊢; exact_mod_cast this
  have h_int : (b₁ : ℤ) - (b₂ : ℤ) = n * (p : ℤ) := by exact_mod_cast h_rat
  have hlt : |(b₁ : ℤ) - b₂| < p := by
    rw [abs_lt]; constructor <;> [push_cast; push_cast] <;> omega
  rw [h_int] at hlt; simp [abs_mul, Nat.abs_cast] at hlt
  have hn0 : n = 0 := by
    by_contra h
    exact absurd hlt (not_lt.mpr (le_mul_of_one_le_left (by omega) (Int.one_le_abs h)))
  simp [hn0] at h_int; omega

set_option maxHeartbeats 1600000 in
/-- **Phase 3 (distinctness upper vs lower)**: The representative `T_p_upper(b)`
does not lie in the same left `Γ₀(N)`-coset as `T_p_lower(p)`. Equivalently,
`T_p_upper(b) ≠ γ * T_p_lower(p)` for any `γ ∈ (Gamma0_pair N).H`.

The proof: `T_p_upper(b) · T_p_lower(p)⁻¹ = [[1/p, b], [0, p]]`. If this equalled
`γ`, the `(0,0)`-entry `1/p` would be an integer. But `p` is prime (so `p ≥ 2`),
so `1/p` is not an integer. -/
lemma T_p_upper_ne_lower_cosets_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (b : ℕ) :
    ∀ γ ∈ (Gamma0_pair N).H,
      (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ≠ γ * T_p_lower p hp.pos := by
  intro γ hγ heq
  -- From heq: γ = T_p_upper(b) * T_p_lower(p)⁻¹
  have hγ_eq : γ = (T_p_upper p hp.pos b : GL (Fin 2) ℚ) *
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)⁻¹ := by
    rw [heq]; group
  rw [hγ_eq, T_p_upper_mul_lower_inv_eq p hp b] at hγ
  obtain ⟨n, hn⟩ := Gamma0_pair_H_entry_is_int _ hγ 0 0
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_np : (n : ℚ) * p = 1 := by rw [← hn]; field_simp
  have h_int : n * (p : ℤ) = 1 := by exact_mod_cast h_np
  have hp_dvd : (p : ℤ) ∣ 1 := ⟨n, by linarith⟩
  have h_le := Int.le_of_dvd one_pos hp_dvd
  linarith [show (1 : ℤ) < ↑p from Int.ofNat_lt.mpr hp.one_lt]

/-! ### Phase 4: bijection `Fin (p+1) ≃ decompQuot (Gamma0_pair N) (rep (D_p_Gamma0))`

The `decompQuot` parameterizes **right** cosets `H · adj(g)` for `g ∈ D_p_Gamma0`.
Phase 3 above established that the `p+1` classical representatives `T_p_upper(b)`
(for `b = 0, …, p-1`) and `T_p_lower(p)` live in distinct **left** Γ₀(N)-cosets;
the adjugate anti-involution `adj(g) = g⁻¹ · det(g)` swaps left and right cosets, so
their adjugates live in distinct right cosets. We package this into a `Fin (p+1)`
indexed function and combine with the `p+1` cardinality from Phase 1 to get the
`Equiv`. -/

/-- Inclusion `(Gamma0_pair N).H ≤ (GL_pair 2).H = SLnZ_subgroup 2`. Γ₀(N) is the
image of the inclusion `Γ₀(N) ↪ SL₂(ℤ)` under `mapGL`. -/
lemma Gamma0_pair_H_le_GL_pair_H (N : ℕ) [NeZero N] :
    (HeckeRing.GLn.Gamma0_pair N).H ≤ (GL_pair 2).H := by
  intro g hg
  obtain ⟨s, _, hs⟩ := Subgroup.mem_map.mp hg
  exact ⟨s, hs⟩

/-- The matrix identity `adj(diag(1,p)) = T_p_lower p`. -/
private lemma adj_diag_1p_eq_T_p_lower (p : ℕ) (hp : Nat.Prime p) :
    GL_adjugate (diagMat 2 ![1, p] : GL (Fin 2) ℚ) = (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  apply Units.ext; ext i j
  have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k => by
    fin_cases k <;> simp [hp.pos]
  simp only [GL_adjugate_val, diagMat_val _ _ hpos]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext x; fin_cases x <;> simp
  have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  fin_cases i <;> fin_cases j <;>
    simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.of_apply, huniv, he0, he1,
      Finset.prod_singleton]

/-- `adj(rep(D_p_Gamma0)) ∈ D_p_Gamma0`: the adjugate of the representative lies
in the double coset. For `D_p_Gamma0 = ⟦diag(1,p)⟧`, `adj(diag(1,p)) = diag(p,1) =
T_p_lower`, which by `T_p_lower_mem_D_p_Gamma0` lies in `D_p_Gamma0`. -/
private lemma adj_rep_mem_D_p_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) ∈
      HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) := by
  -- rep ∈ D_p_Gamma0, so rep = a * diag(1,p) * c with a, c ∈ H
  have hrep := HeckeCoset.rep_mem (D_p_Gamma0 N p hp.pos)
  rw [D_p_Gamma0, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, hrep_eq⟩ := hrep
  -- adj(diag(1,p)) = T_p_lower ∈ D_p_Gamma0
  have hTl := T_p_lower_mem_D_p_Gamma0 N p hp hpN
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hTl
  obtain ⟨b₁, hb₁, b₂, hb₂, hTl_eq⟩ := hTl
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  have hadj_diag := adj_diag_1p_eq_T_p_lower p hp
  -- adj(rep) = adj(a * diag * c) = adj(c) * adj(diag) * adj(a)
  -- with adj(diag) = T_p_lower = b₁ * rep * b₂.
  refine ⟨GL_adjugate c * b₁,
    (HeckeRing.GLn.Gamma0_pair N).H.mul_mem
      (HeckePairAction.adjugate_mem_H c hc) hb₁,
    b₂ * GL_adjugate a,
    (HeckeRing.GLn.Gamma0_pair N).H.mul_mem hb₂
      (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  have h1 : GL_adjugate (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
      GL_adjugate c * GL_adjugate (diagMat 2 ![1, p]) * GL_adjugate a := by
    conv_lhs => rw [show (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) =
      a * diagMat 2 ![1, p] * c from hrep_eq]
    rw [GL_adjugate_mul, GL_adjugate_mul, mul_assoc]
  rw [h1, hadj_diag, hTl_eq]; group

/-- Generic: if `adj(rep(D)) ∈ toSet D`, then for any `g ∈ toSet D`, `adj(g) ∈ toSet D`.
Uses anti-multiplicativity of adj and closure of `H` under adj
(`HeckePairAction.adjugate_mem_H`). -/
private lemma GL_adjugate_mem_toSet_Gamma0 (N : ℕ) [NeZero N]
    (D : HeckeCoset (HeckeRing.GLn.Gamma0_pair N))
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet D)
    (hadj_rep : GL_adjugate (HeckeCoset.rep D : GL _ ℚ) ∈ HeckeCoset.toSet D) :
    GL_adjugate g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hg hadj_rep ⊢
  obtain ⟨a, ha, c, hc, heq⟩ := hg
  obtain ⟨r₁, hr₁, r₂, hr₂, hrep_eq⟩ := hadj_rep
  refine ⟨GL_adjugate c * r₁,
    (HeckeRing.GLn.Gamma0_pair N).H.mul_mem
      (HeckePairAction.adjugate_mem_H c hc) hr₁,
    r₂ * GL_adjugate a,
    (HeckeRing.GLn.Gamma0_pair N).H.mul_mem hr₂
      (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  rw [heq, GL_adjugate_mul, GL_adjugate_mul]
  rw [show GL_adjugate (HeckeCoset.rep D : GL _ ℚ) =
    r₁ * (HeckeCoset.rep D : GL _ ℚ) * r₂ from hrep_eq]
  group

/-- For `g ∈ toSet(D_p_Gamma0)`, there exist `h₁, h₂ ∈ (Gamma0_pair N).H` with
`adj(g) = h₁ · rep(D_p_Gamma0) · h₂`. -/
private noncomputable def adj_mem_dc_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos)) :
    ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
      (h₂ : GL _ ℚ) (_ : h₂ ∈ (HeckeRing.GLn.Gamma0_pair N).H),
      GL_adjugate g =
        h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ := by
  have hadj_rep := adj_rep_mem_D_p_Gamma0 N p hp hpN
  have := GL_adjugate_mem_toSet_Gamma0 N (D_p_Gamma0 N p hp.pos) g hg hadj_rep
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
  obtain ⟨a, ha, b, hb, heq⟩ := this; exact ⟨a, ha, b, hb, heq⟩

/-- Quotient equality lifting: if `⟦⟨a₁,_⟩⟧ = ⟦⟨a₂,_⟩⟧` in `decompQuot` and
`adj(gᵢ) = aᵢ · rep · cᵢ`, then `adj(g₁)⁻¹ · adj(g₂) ∈ H`. -/
private lemma h_quot_imp_adj_mem_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : Nat.Prime p)
    (a₁ : GL _ ℚ) (ha₁ : a₁ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
    (c₁ : GL _ ℚ) (hc₁ : c₁ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
    (a₂ : GL _ ℚ) (ha₂ : a₂ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
    (c₂ : GL _ ℚ) (hc₂ : c₂ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
    (g₁ g₂ : GL _ ℚ)
    (heq₁ : GL_adjugate g₁ =
      a₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * c₁)
    (heq₂ : GL_adjugate g₂ =
      a₂ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * c₂)
    (hquot : (⟦(⟨a₁, ha₁⟩ : (HeckeRing.GLn.Gamma0_pair N).H)⟧ :
        decompQuot (HeckeRing.GLn.Gamma0_pair N)
          (HeckeCoset.rep (D_p_Gamma0 N p hp.pos))) = ⟦⟨a₂, ha₂⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (HeckeRing.GLn.Gamma0_pair N).H := by
  rw [heq₁, heq₂]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf] at hrel
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at hrel
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have h_prod :
      (a₁ * ↑(HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) * c₁)⁻¹ *
        (a₂ * ↑(HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) * c₂) =
      c₁⁻¹ * ((↑(HeckeCoset.rep (D_p_Gamma0 N p hp.pos)))⁻¹ * (a₁⁻¹ * a₂) *
        ↑(HeckeCoset.rep (D_p_Gamma0 N p hp.pos))) * c₂ := by group
  rw [h_prod]
  exact (HeckeRing.GLn.Gamma0_pair N).H.mul_mem
    ((HeckeRing.GLn.Gamma0_pair N).H.mul_mem
      ((HeckeRing.GLn.Gamma0_pair N).H.inv_mem hc₁) hrel) hc₂

/-- `adj(T_p_upper(b₁))⁻¹ · adj(T_p_upper(b₂)) ∉ (Gamma0_pair N).H` for distinct
`b₁, b₂ < p`. Follows from the level-1 version since `(Gamma0_pair N).H ≤
(GL_pair 2).H`. -/
private lemma adj_upper_inv_mul_upper_not_mem_Gamma0 (N : ℕ) [NeZero N] (p : ℕ)
    (hp : Nat.Prime p) (b₁ b₂ : ℕ) (hb₁ : b₁ < p) (hb₂ : b₂ < p) (hne : b₁ ≠ b₂) :
    (GL_adjugate (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b₂ : GL (Fin 2) ℚ) ∉
       (HeckeRing.GLn.Gamma0_pair N).H := by
  intro hmem
  exact adj_upper_inv_mul_not_mem_H p hp b₁ b₂ hb₁ hb₂ hne
    (Gamma0_pair_H_le_GL_pair_H N hmem)

/-- `adj(T_p_upper(b))⁻¹ · adj(T_p_lower) ∉ (Gamma0_pair N).H`. Lifted from the
level-1 lemma via `Gamma0_pair_H_le_GL_pair_H`. -/
private lemma adj_upper_inv_mul_lower_not_mem_Gamma0 (N : ℕ) [NeZero N] (p : ℕ)
    (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∉
       (HeckeRing.GLn.Gamma0_pair N).H := by
  intro hmem
  exact adj_upper_inv_mul_lower_not_mem_H p hp b (Gamma0_pair_H_le_GL_pair_H N hmem)

/-- `adj(T_p_lower)⁻¹ · adj(T_p_upper(b)) ∉ (Gamma0_pair N).H`. Lifted from the
level-1 lemma via `Gamma0_pair_H_le_GL_pair_H`. -/
private lemma adj_lower_inv_mul_upper_not_mem_Gamma0 (N : ℕ) [NeZero N] (p : ℕ)
    (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∉
       (HeckeRing.GLn.Gamma0_pair N).H := by
  intro hmem
  exact adj_lower_inv_mul_upper_not_mem_H p hp b (Gamma0_pair_H_le_GL_pair_H N hmem)

/-- **Target lemma**: The `p+1` classical representatives `T_p_upper(b)` (for
`b = 0, …, p-1`) and `T_p_lower(p)` give a bijection `Fin (p+1) ≃ decompQuot
(Gamma0_pair N) (rep (D_p_Gamma0 N p))` via the adjugate anti-involution.

This is the Γ₀(N)-level analogue of `tRep_gen_D_p_matches_T_p_reps` at level 1:
combining the Phase 1 cardinality (`HeckeCoset_deg_D_p_Gamma0 = p + 1`) and the
Phase 3 distinctness lemmas yields a bijection. -/
noncomputable def T_p_coset_reps_Gamma0_equiv (N : ℕ) [NeZero N] (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    Fin (p + 1) ≃ decompQuot (HeckeRing.GLn.Gamma0_pair N)
      (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) := by
  -- Factorisations of adj at the reps.
  have h_upper_dc : ∀ b : Fin p,
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
        (h₂ : GL _ ℚ) (_ : h₂ ∈ (HeckeRing.GLn.Gamma0_pair N).H),
        GL_adjugate (T_p_upper p hp.pos b.val : GL _ ℚ) =
          h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ := fun b =>
    adj_mem_dc_Gamma0 N p hp hpN _ (T_p_upper_mem_D_p_Gamma0 N p hp b.val)
  have h_lower_dc :
      ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (HeckeRing.GLn.Gamma0_pair N).H)
        (h₂ : GL _ ℚ) (_ : h₂ ∈ (HeckeRing.GLn.Gamma0_pair N).H),
        GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
          h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL _ ℚ) * h₂ :=
    adj_mem_dc_Gamma0 N p hp hpN _ (T_p_lower_mem_D_p_Gamma0 N p hp hpN)
  -- Define φ : Fin(p+1) → decompQuot.
  let φ : Fin (p + 1) →
      decompQuot (HeckeRing.GLn.Gamma0_pair N)
        (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) := fun j =>
    if h : j.val < p then
      ⟦⟨(h_upper_dc ⟨j.val, h⟩).choose,
        (h_upper_dc ⟨j.val, h⟩).choose_spec.choose⟩⟧
    else
      ⟦⟨h_lower_dc.choose, h_lower_dc.choose_spec.choose⟩⟧
  -- Injectivity of φ via h_quot_imp_adj_mem_Gamma0 + adj_*_not_mem_Gamma0.
  have h_inj : Function.Injective φ := by
    intro j₁ j₂ heq
    by_contra hne
    simp only [φ] at heq
    by_cases h₁ : j₁.val < p <;> by_cases h₂ : j₂.val < p
    · -- Both upper.
      simp only [h₁, h₂, dite_true] at heq
      have hne_val : j₁.val ≠ j₂.val := fun h => hne (Fin.ext h)
      set e₁ := h_upper_dc ⟨j₁.val, h₁⟩
      set e₂ := h_upper_dc ⟨j₂.val, h₂⟩
      have hmem := h_quot_imp_adj_mem_Gamma0 N p hp
        e₁.choose e₁.choose_spec.choose
        e₁.choose_spec.choose_spec.choose
          e₁.choose_spec.choose_spec.choose_spec.choose
        e₂.choose e₂.choose_spec.choose
        e₂.choose_spec.choose_spec.choose
          e₂.choose_spec.choose_spec.choose_spec.choose
        (T_p_upper p hp.pos j₁.val) (T_p_upper p hp.pos j₂.val)
        e₁.choose_spec.choose_spec.choose_spec.choose_spec
        e₂.choose_spec.choose_spec.choose_spec.choose_spec
        heq
      exact adj_upper_inv_mul_upper_not_mem_Gamma0 N p hp j₁.val j₂.val h₁ h₂
        hne_val hmem
    · -- j₁ upper, j₂ lower.
      simp only [h₁, dite_true, h₂, dite_false] at heq
      set e₁ := h_upper_dc ⟨j₁.val, h₁⟩
      have hmem := h_quot_imp_adj_mem_Gamma0 N p hp
        e₁.choose e₁.choose_spec.choose
        e₁.choose_spec.choose_spec.choose
          e₁.choose_spec.choose_spec.choose_spec.choose
        h_lower_dc.choose h_lower_dc.choose_spec.choose
        h_lower_dc.choose_spec.choose_spec.choose
          h_lower_dc.choose_spec.choose_spec.choose_spec.choose
        (T_p_upper p hp.pos j₁.val) (T_p_lower p hp.pos)
        e₁.choose_spec.choose_spec.choose_spec.choose_spec
        h_lower_dc.choose_spec.choose_spec.choose_spec.choose_spec
        heq
      exact adj_upper_inv_mul_lower_not_mem_Gamma0 N p hp j₁.val hmem
    · -- j₁ lower, j₂ upper.
      simp only [h₁, dite_false, h₂, dite_true] at heq
      set e₂ := h_upper_dc ⟨j₂.val, h₂⟩
      have hmem := h_quot_imp_adj_mem_Gamma0 N p hp
        h_lower_dc.choose h_lower_dc.choose_spec.choose
        h_lower_dc.choose_spec.choose_spec.choose
          h_lower_dc.choose_spec.choose_spec.choose_spec.choose
        e₂.choose e₂.choose_spec.choose
        e₂.choose_spec.choose_spec.choose
          e₂.choose_spec.choose_spec.choose_spec.choose
        (T_p_lower p hp.pos) (T_p_upper p hp.pos j₂.val)
        h_lower_dc.choose_spec.choose_spec.choose_spec.choose_spec
        e₂.choose_spec.choose_spec.choose_spec.choose_spec
        heq
      exact adj_lower_inv_mul_upper_not_mem_Gamma0 N p hp j₂.val hmem
    · -- Both ≥ p, but j₁, j₂ : Fin (p+1) so j₁.val = p = j₂.val.
      have := j₁.isLt; have := j₂.isLt; omega
  -- The source is Fin (p+1) with cardinality p+1 and the target has p+1 elements
  -- by HeckeCoset_deg_D_p_Gamma0; so an injective map is a bijection.
  have h_card :
      Fintype.card (decompQuot (HeckeRing.GLn.Gamma0_pair N)
        (HeckeCoset.rep (D_p_Gamma0 N p hp.pos))) = p + 1 := by
    have h := HeckeCoset_deg_D_p_Gamma0 N p hp hpN
    rw [Nat.card_eq_fintype_card] at h; exact h
  have h_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨h_inj, by rw [Fintype.card_fin, h_card]⟩
  exact Equiv.ofBijective φ h_bij

end HeckeRing.GL2
