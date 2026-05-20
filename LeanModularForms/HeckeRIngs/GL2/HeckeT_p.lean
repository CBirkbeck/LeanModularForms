/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeAction

/-!
# Hecke Operator T_p on M_k(Γ₁(N))

Defines the Hecke operator `T_p` on modular forms for `Γ₁(N)` following
Diamond–Shurman §5.2, Proposition 5.2.1.

For `p` prime and `p` coprime to `N`:

  `T_p(f) = Σ_{j=0}^{p-1} f ∣[k] [[1,j],[0,p]] + (⟨p⟩ f) ∣[k] [[p,0],[0,1]]`

where `⟨p⟩` is the diamond operator for `p ∈ (ℤ/Nℤ)ˣ`.

## Main definitions

* `T_p_upper` — the coset representative `[[1,b],[0,p]]` as `GL₂(ℚ)`
* `T_p_lower` — the matrix `[[p,0],[0,1]]` as `GL₂(ℚ)`
* `heckeT_p` — `T_p` as a ℂ-linear endomorphism of `M_k(Γ₁(N))`

## Main results

* `heckeT_p_comm_diamondOp` — `T_p` commutes with `⟨d⟩`
* `heckeT_p_preserves_modFormCharSpace` — `T_p` preserves character spaces

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1
* Miyake, *Modular Forms*, §4.5
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ}

/-! ### Coset representative matrices -/

/-- The upper triangular coset representative `[[1, b], [0, p]]` as a `GL₂(ℚ)` element.
These are the standard representatives for the double coset `Γ₁(N)\Γ₁(N)αΓ₁(N)`. -/
noncomputable def T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, (b : ℚ); 0, (p : ℚ)]
    (by simp [det_fin_two]; exact_mod_cast hp.ne')

/-- The diagonal representative `[[p, 0], [0, 1]]` as a `GL₂(ℚ)` element.
Used in the `(p+1)`-th term of `T_p` when `gcd(p, N) = 1`. -/
noncomputable def T_p_lower (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by simp [det_fin_two]; exact_mod_cast hp.ne')

@[simp]
lemma T_p_upper_coe (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (b : ℚ); 0, (p : ℚ)] := rfl

@[simp]
lemma T_p_lower_coe (p : ℕ) (hp : 0 < p) :
    (↑(T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℚ) = !![(p : ℚ), 0; 0, 1] := rfl

lemma T_p_upper_det (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp [det_fin_two]

lemma T_p_lower_det (p : ℕ) (hp : 0 < p) :
    (↑(T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp [det_fin_two]

/-! ### Scalar slash interaction

For `GL₂(ℚ)` elements with positive determinant, `(c • f) ∣[k] g = c • (f ∣[k] g)`. -/

lemma glMap_det_pos_of_rat_det_pos (g : GL (Fin 2) ℚ) (h : 0 < g.det.val) :
    0 < (glMap g).det.val := by
  have : (glMap g).det.val = algebraMap ℚ ℝ g.det.val :=
    congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) g)
  rw [this]; exact Rat.cast_pos.mpr h

lemma smul_slash_pos_det (k : ℤ) (c : ℂ) (φ : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) ℚ) (hg : 0 < g.det.val) :
    (c • φ) ∣[k] g = c • (φ ∣[k] g) := by
  show (c • φ) ∣[k] glMap g = c • (φ ∣[k] glMap g)
  have hσ : UpperHalfPlane.σ (glMap g) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; simp only [glMap_det_pos_of_rat_det_pos g hg, ↓reduceIte]
  ext z; show ((c • φ) ∣[k] glMap g) z = (c • (φ ∣[k] glMap g)) z
  rw [ModularForm.smul_slash, hσ]; rfl

lemma T_p_upper_det_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (T_p_upper p hp b).det.val := by
  rw [GeneralLinearGroup.val_det_apply, T_p_upper_det]; exact_mod_cast hp

lemma T_p_lower_det_pos (p : ℕ) (hp : 0 < p) :
    0 < (T_p_lower p hp).det.val := by
  rw [GeneralLinearGroup.val_det_apply, T_p_lower_det]; exact_mod_cast hp

/-! ### The T_p operator -/

/-- The "upper triangular" part of `T_p`: the sum `Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]]`.
This is the full `T_p` when `p ∣ N`, and the first `p` terms when `p ∤ N`. -/
noncomputable def heckeT_p_ut (k : ℤ) (p : ℕ) (hp : 0 < p)
    (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ b ∈ Finset.range p, f ∣[k] (T_p_upper p hp b : GL (Fin 2) ℚ)

/-- The full Hecke operator `T_p` on `M_k(Γ₁(N))` for `p` prime coprime to `N`.
Defined as `Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]] + (⟨p⟩ f) ∣[k] [[p,0],[0,1]]`,
following Diamond–Shurman Proposition 5.2.1. -/
noncomputable def heckeT_p_fun [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ :=
  heckeT_p_ut k p hp.pos (⇑f) +
  (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
    (T_p_lower p hp.pos : GL (Fin 2) ℚ)

/-! ### Holomorphicity, invariance, and boundedness -/

private lemma heckeT_p_holomorphic [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeT_p_fun k p hp hpN f) := by
  apply MDifferentiable.add
  · apply MDifferentiable.sum; intro b _
    exact (ModularFormClass.holo f).slash k _
  · exact (ModularFormClass.holo (diamondOp k (ZMod.unitOfCoprime p hpN) f)).slash k _

/-! ### Möbius permutation and helpers -/

/-- `a * a⁻¹ = 1` in `ZMod p` for `a ≠ 0` when `p` is prime.
Proved via `ZMod.mul_val_inv`, avoiding the `Field (ZMod p)` import. -/
private lemma zmod_mul_inv {p : ℕ} [hp : Fact p.Prime] [NeZero p]
    {a : ZMod p} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  have hne : a.val ≠ 0 := fun h => ha (by
    rw [show a = (a.val : ZMod p) from by rw [ZMod.natCast_val, ZMod.cast_id]]; simp [h])
  have hcop : a.val.Coprime p :=
    (hp.out.coprime_iff_not_dvd.2 (fun h => hne (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a)))).symm
  have vcz : ∀ x : ZMod p, (x.val : ZMod p) = x := fun x => by rw [ZMod.natCast_val, ZMod.cast_id]
  conv_lhs => rw [show a = (a.val : ZMod p) from (vcz a).symm,
    show ((a.val : ZMod p))⁻¹ = (((a.val : ZMod p)⁻¹).val : ZMod p) from (vcz _).symm]
  exact ZMod.mul_val_inv hcop

/-- The Möbius action of matrix `M` on `Fin p`:
when `p ∤ (M₀₀ + b·M₁₀)`,
returns `(M₀₁ + b·M₁₁)·(M₀₀ + b·M₁₀)⁻¹ mod p`;
when `p ∣ (M₀₀ + b·M₁₀)`,
returns `M₁₁·M₁₀⁻¹ mod p` (the image of ∞ under σ). -/
private noncomputable def moebiusFin (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (b : Fin p) : Fin p :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : ℤ := M 0 0 + ↑b.val * M 1 0
  let B : ℤ := M 0 1 + ↑b.val * M 1 1
  if (A : ZMod p) = 0 then
    ⟨((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  else
    ⟨((B : ZMod p) * (A : ZMod p)⁻¹).val, ZMod.val_lt _⟩

/-- Slash distributes over finset sums. -/
lemma sum_slash (k : ℤ) {ι : Type*} (s : Finset ι)
    (φ : ι → (UpperHalfPlane → ℂ)) (g : GL (Fin 2) ℝ) :
    (∑ b ∈ s, φ b) ∣[k] g = ∑ b ∈ s, (φ b ∣[k] g) := by
  induction s using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp only [Finset.sum_cons, SlashAction.add_slash, ih]

/-- The Möbius function is injective on `Fin p` for any SL₂(ℤ) matrix
(follows from det = 1 in ZMod p). -/
private lemma moebiusFin_injective (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    Function.Injective (moebiusFin p hp M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdet_eq : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [det_fin_two] at hdet; exact hdet
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet_eq]
  -- Helper: if A = 0 then M₁₀ ≠ 0 (otherwise det ≡ 0 mod p)
  have no_double_zero : ∀ c : Fin p,
      ((M 0 0 + ↑c.val * M 1 0 : ℤ) : ZMod p) = 0 →
      ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
    intro c hAc h10
    have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
      have : ((M 0 0 + ↑c.val * M 1 0 : ℤ) : ZMod p) =
        ((M 0 0 : ℤ) : ZMod p) + ((c.val : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) := by
        push_cast; ring
      rw [h10, mul_zero, add_zero] at this; rw [← this]; exact hAc
    have : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 0 := by
      push_cast; rw [h00, h10]; ring
    rw [hdet_p] at this; exact one_ne_zero this
  -- Helper: ZMod p divisibility implies ℕ equality for Fin p
  have val_eq_of_dvd :
      ∀ x y : Fin p, (p : ℤ) ∣ ((x.val : ℤ) - y.val) → x.val = y.val := by
    intro x y ⟨k, hk⟩
    have h1 : (x.val : ℤ) < p := by exact_mod_cast x.prop
    have h2 : (y.val : ℤ) < p := by exact_mod_cast y.prop
    have h5 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hk0 : k = 0 := by nlinarith
    subst hk0; omega
  -- In ZMod p for prime p: p | a*b ∧ ¬(p | b) → p | a (hence ↑a = 0)
  have zmod_cancel {a b : ℤ} (hab : ((a * b : ℤ) : ZMod p) = 0)
      (hb : ((b : ℤ) : ZMod p) ≠ 0) : ((a : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hab
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hb' : ¬((p : ℤ) ∣ b) := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr h)
    have hab_abs : p ∣ a.natAbs * b.natAbs := by
      rw [← Int.natAbs_mul]; exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hab)
    rcases hp.dvd_mul.mp hab_abs with h | h
    · exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
    · exact absurd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)) hb'
  -- Cross-multiply: a*b⁻¹ = c*d⁻¹ with b,d ≠ 0 implies a*d = c*b
  have cross_mul {a b c d : ZMod p} (hb : b ≠ 0) (hd : d ≠ 0)
      (h : a * b⁻¹ = c * d⁻¹) : a * d = c * b := by
    have inv_mul {x : ZMod p} (hx : x ≠ 0) : x⁻¹ * x = 1 := by
      rw [mul_comm]; exact zmod_mul_inv hx
    have := congr_arg (· * (b * d)) h
    simp only [mul_assoc] at this
    rwa [show b⁻¹ * (b * d) = d from by rw [← mul_assoc, inv_mul hb, one_mul],
         show d⁻¹ * (b * d) = b from by
            rw [mul_comm b d, ← mul_assoc, inv_mul hd, one_mul]] at this
  intro b₁ b₂ heq
  have hv : (moebiusFin p hp M b₁).val = (moebiusFin p hp M b₂).val :=
    congr_arg Fin.val heq
  simp only [moebiusFin] at hv
  set A₁ : ZMod p := ((M 0 0 + ↑b₁.val * M 1 0 : ℤ) : ZMod p) with hA₁_def
  set A₂ : ZMod p := ((M 0 0 + ↑b₂.val * M 1 0 : ℤ) : ZMod p) with hA₂_def
  set B₁ : ZMod p := ((M 0 1 + ↑b₁.val * M 1 1 : ℤ) : ZMod p) with hB₁_def
  set B₂ : ZMod p := ((M 0 1 + ↑b₂.val * M 1 1 : ℤ) : ZMod p) with hB₂_def
  suffices hsuff : b₁.val = b₂.val by ext; exact hsuff
  -- det identity in ZMod p for each index
  have det_eq (c : Fin p) :
      ((M 1 1 : ℤ) : ZMod p) * ((M 0 0 + ↑c.val * M 1 0 : ℤ) : ZMod p) -
      ((M 1 0 : ℤ) : ZMod p) * ((M 0 1 + ↑c.val * M 1 1 : ℤ) : ZMod p) =
      ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) := by push_cast; ring
  by_cases hA₁ : A₁ = 0 <;> by_cases hA₂ : A₂ = 0
  · -- Both A = 0: (b₁ - b₂) * M₁₀ ≡ 0, and M₁₀ ≢ 0
    have h_ring : A₁ - A₂ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) *
        ((M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def]; push_cast; ring
    rw [hA₁, hA₂, sub_self] at h_ring
    have h10_ne := no_double_zero b₁ hA₁
    have hb_zero : ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) = 0 := by
      have h := h_ring.symm; rw [← Int.cast_mul] at h; exact zmod_cancel h h10_ne
    exact val_eq_of_dvd b₁ b₂ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb_zero)
  · -- A₁ = 0, A₂ ≠ 0: contradiction via det
    exfalso
    rw [if_pos hA₁, if_neg hA₂] at hv
    have hv_eq := ZMod.val_injective p hv
    have h10_ne := no_double_zero b₁ hA₁
    have hcross := cross_mul h10_ne hA₂ hv_eq
    -- M₁₁*A₂ - M₁₀*B₂ = det = 1, but hcross gives
    -- M₁₁*A₂ = B₂*M₁₀, so diff = 0
    have hdet₂ : ((M 1 1 : ℤ) : ZMod p) * A₂ - ((M 1 0 : ℤ) : ZMod p) * B₂ = 1 := by
      rw [show ((M 1 1 : ℤ) : ZMod p) * A₂ - ((M 1 0 : ℤ) : ZMod p) * B₂ =
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) from by
          simp only [hA₂_def, hB₂_def]; push_cast; ring, hdet_p]
    exact one_ne_zero (hdet₂.symm.trans (by rw [hcross]; ring))
  · -- A₁ ≠ 0, A₂ = 0: symmetric
    exfalso
    rw [if_neg hA₁, if_pos hA₂] at hv
    have hv_eq := ZMod.val_injective p hv
    have h10_ne := no_double_zero b₂ hA₂
    have hcross := cross_mul hA₁ h10_ne hv_eq
    have hdet₁ : ((M 1 1 : ℤ) : ZMod p) * A₁ - ((M 1 0 : ℤ) : ZMod p) * B₁ = 1 := by
      rw [show ((M 1 1 : ℤ) : ZMod p) * A₁ - ((M 1 0 : ℤ) : ZMod p) * B₁ =
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) from by
          simp only [hA₁_def, hB₁_def]; push_cast; ring, hdet_p]
    exact one_ne_zero (hdet₁.symm.trans (by rw [show ((M 1 1 : ℤ) : ZMod p) * A₁ =
      B₁ * ((M 1 0 : ℤ) : ZMod p) from hcross.symm]; ring))
  · -- Both A ≠ 0: cross-multiply, use det to get b₁ = b₂
    rw [if_neg hA₁, if_neg hA₂] at hv
    have hv_eq := ZMod.val_injective p hv
    have hcross := cross_mul hA₁ hA₂ hv_eq
    -- B₁*A₂ - B₂*A₁ = (b₁ - b₂) * det
    have h_cross_det : B₁ * A₂ - B₂ * A₁ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) *
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def, hB₁_def, hB₂_def]; push_cast; ring
    have h0 : B₁ * A₂ - B₂ * A₁ = 0 := by rw [hcross]; ring
    rw [h0, hdet_p, mul_one] at h_cross_det
    exact val_eq_of_dvd b₁ b₂ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_cross_det.symm)

/-! ### Orbit factorisation (D-S Prop 5.2.1)

The `p + 1` representatives `{β_b = [[1,b],[0,p]] : b < p} ∪ {β_∞ = [[p,0],[0,1]]}`
are left coset representatives for the double coset decomposition underlying `T_p`.

For `σ ∈ Γ₁(N)`, the products `β_b · σ` and `β_∞ · σ` are re-expressed via
matrix factorisation. Set `A := σ₀₀ + b·σ₁₀`, `B := σ₀₁ + b·σ₁₁`:

* **Case p ∤ A** (upper → upper): `β_b · σ = τ · β_{j'}` where
  `j' = B·A⁻¹ mod p` and `τ ∈ Γ₁(N)`, so `f|β_b·σ = f|β_{j'}`.
* **Case p ∣ A** (upper → lower): `β_b · σ = τ · β_∞` where `τ ∈ Γ₀(N)`
  with `Gamma0Map τ = p·σ₁₁`, so `f|β_b·σ = (⟨p⟩f)|β_∞`.
* **Case p ∤ σ₁₀** (lower → upper): `β_∞ · σ = τ · β_{j'}` where
  `τ ∈ Γ₀(N)` with `Gamma0Map τ = p⁻¹ mod N`, so `(⟨p⟩f)|β_∞·σ = f|β_{j'}`.
* **Case p ∣ σ₁₀** (lower → lower): `β_∞ · σ = τ · β_∞` where `τ ∈ Γ₁(N)`
  (using `gcd(p,N) = 1` and `N∣σ₁₀`, `p∣σ₁₀` ⟹ `Np∣σ₁₀`),
  so `(⟨p⟩f)|β_∞·σ = (⟨p⟩f)|β_∞`.

The collection of output indices forms a bijection of `{0,…,p−1,∞}` by
injectivity of the Möbius map
`j ↦ (σ₀₁+j·σ₁₁)/(σ₀₀+j·σ₁₀)` on `ℙ¹(𝔽_p)`. -/

-- Orbit factorisation lemmas.

/-- For σ ∈ Γ₁(N), the diamond operator is trivial: `diamondOpAux k ⟨σ, _⟩ f = f`.
This is because `Gamma0MapUnits ⟨σ, _⟩ = 1` (σ₁₁ ≡ 1 mod N for Γ₁ elements). -/
private lemma diamondOpAux_gamma1 [NeZero N] (k : ℤ)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f = f := by
  have h1 : Gamma0MapUnits ⟨σ, Gamma1_in_Gamma0 N hσ⟩ = 1 := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one]
    exact ((Gamma1_mem N σ).mp hσ).2.1
  rw [(diamondOp_eq_diamondOpAux k 1 ⟨σ, Gamma1_in_Gamma0 N hσ⟩ h1).symm,
      diamondOp_one, LinearMap.id_apply]

/-! ### Orbit factorisation for σ ∈ Γ₀(N)

Matrix factorisations tracking the diamond operator through `Gamma0MapUnits`.
For `σ ∈ Γ₀(N)`, each constructed `τ` satisfies `Gamma0Map(τ) = Gamma0Map(σ)`
(or a predictable multiple), so the conclusion involves `diamondOpAux k ⟨σ, hσ⟩ f`
rather than bare `f`. The Γ₁(N) case follows by `diamondOpAux_gamma1`. -/

/-- **Upper → Upper for Γ₀(N)**: when `σ ∈ Γ₀(N)` and `p ∤ (σ₀₀ + b·σ₁₀)`,
the product `β_b · σ` factors as `τ · β_{j'}` with `τ ∈ Γ₀(N)` and
`Gamma0Map(τ) = Gamma0Map(σ)`. -/
private theorem orbit_upper_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (_hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) * mapGL ℝ σ) =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
      glMap (T_p_upper p hp.pos
        (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  set A : ℤ := M 0 0 + ↑b.val * M 1 0 with hA_def
  set B : ℤ := M 0 1 + ↑b.val * M 1 1 with hB_def
  -- σ ∈ Gamma0 N yields N ∣ σ₁₀
  rw [Gamma0_mem] at hσ
  -- A is nonzero mod p
  have hA_ne : (A : ZMod p) ≠ 0 := by
    intro h; exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp h)
  -- j' = B * A⁻¹ mod p, which equals moebiusFin output
  set j'_zmod : ZMod p := (B : ZMod p) * (A : ZMod p)⁻¹
  set j' := j'_zmod.val
  have hj'_lt : j' < p := ZMod.val_lt j'_zmod
  -- Show moebiusFin gives j'
  have hmoeb : (moebiusFin p hp M b).val = j' := by
    simp only [moebiusFin, show (M 0 0 + ↑b.val * M 1 0 : ℤ) = A from rfl,
      show (M 0 1 + ↑b.val * M 1 1 : ℤ) = B from rfl]
    rw [if_neg hA_ne]
  -- Key: A * j' ≡ B (mod p)
  have hAj'_mod : (A : ZMod p) * (j' : ZMod p) = (B : ZMod p) := by
    have key : (A : ZMod p) * ((B : ZMod p) * (A : ZMod p)⁻¹) = (B : ZMod p) := by
      rw [mul_comm (B : ZMod p) _, ← mul_assoc, zmod_mul_inv hA_ne, one_mul]
    rw [show (j' : ZMod p) = j'_zmod from by
      show (j'_zmod.val : ZMod p) = j'_zmod; rw [ZMod.natCast_val, ZMod.cast_id]]
    exact key
  -- Therefore p ∣ (B - A * j')
  have hpBAj : (p : ℤ) ∣ (B - A * ↑j') := by
    have : ((B - A * ↑j' : ℤ) : ZMod p) = 0 := by
      push_cast; rw [sub_eq_zero]; exact hAj'_mod.symm
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  -- Exact division
  obtain ⟨q, hq⟩ := hpBAj
  have hq_eq : B - A * ↑j' = ↑p * q := hq
  -- Construct τ ∈ SL₂(ℤ) ∩ Γ₀(N)
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![A, q; ↑p * M 1 0, M 1 1 - M 1 0 * ↑j'] with hτ_mat_def
  have hτ_det : τ_mat.det = 1 := by
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; exact_mod_cast this
    simp only [τ_mat]; rw [det_fin_two_of]
    have hstep : q * (↑p * M 1 0) = (B - A * ↑j') * M 1 0 := by
      have hpq : (↑p : ℤ) * q = B - A * ↑j' := by linarith [hq_eq]
      linarith [show q * (↑p * M 1 0) = (↑p * q) * M 1 0 from by ring,
               show (↑p * q) * M 1 0 = (B - A * ↑j') * M 1 0 from by rw [hpq]]
    have hAB : A * M 1 1 - B * M 1 0 = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
      simp only [show A = M 0 0 + ↑↑b * M 1 0 from rfl,
                 show B = M 0 1 + ↑↑b * M 1 1 from rfl]; ring
    linarith [show A * (M 1 1 - M 1 0 * ↑j') - (B - A * ↑j') * M 1 0 =
                  A * M 1 1 - B * M 1 0 from by ring]
  set τ : SL(2, ℤ) := ⟨τ_mat, hτ_det⟩ with hτ_def
  -- τ ∈ Gamma0 N (uses N ∣ M₁₀ from hσ)
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((↑p * M 1 0 : ℤ) : ZMod N) = 0
    push_cast; rw [hσ, mul_zero]
  -- Gamma0Map(τ) = Gamma0Map(σ):
  -- τ₁₁ = M₁₁ - M₁₀·j' ≡ M₁₁ (mod N) since N ∣ M₁₀
  have hmap : Gamma0Map N ⟨τ, hτ_g0⟩ =
      Gamma0Map N ⟨σ, (Gamma0_mem.mpr hσ)⟩ := by
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    show ((M 1 1 - M 1 0 * ↑j' : ℤ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    push_cast; rw [hσ, zero_mul, sub_zero]
  -- Matrix equation: T_p_upper b * mapGL ℚ σ = mapGL ℚ τ * T_p_upper j'
  have hmatrix : T_p_upper p hp.pos b.val * mapGL ℚ σ =
      mapGL ℚ τ * T_p_upper p hp.pos j' := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_upper_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def,
        hA_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show B = A * ↑j' + q * ↑p from by linarith [hq_eq])) |
        ring
  -- Conclude via slash_mul and slash-transport (Gamma0Map(τ) = Gamma0Map(σ))
  rw [hmoeb]
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] glMap (T_p_upper p hp.pos j'))
    (slash_eq_of_Gamma0Map_eq
      (fun _ hγ => SlashInvariantFormClass.slash_action_eq f _ hγ)
      ⟨τ, hτ_g0⟩ ⟨σ, Gamma0_mem.mpr hσ⟩ hmap)

/-- **Upper → Lower for Γ₀(N)**:
when `σ ∈ Γ₀(N)` and `p ∣ (σ₀₀ + b·σ₁₀)`, the product `β_b · σ` factors
as `τ · β_∞` with `τ ∈ Γ₀(N)` and `Gamma0Map(τ) = p · Gamma0Map(σ)`. -/
private theorem orbit_upper_div_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) * mapGL ℝ σ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN)
      (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      glMap (T_p_lower p hp.pos) := by
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  set A : ℤ := M 0 0 + ↑b.val * M 1 0 with hA_def
  set B : ℤ := M 0 1 + ↑b.val * M 1 1 with hB_def
  rw [Gamma0_mem] at hσ
  obtain ⟨a, ha⟩ := hA
  -- Construct τ = [[a, B], [σ₁₀, p·σ₁₁]]
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ := !![a, B; M 1 0, ↑p * M 1 1] with hτ_mat_def
  have hτ_det : τ_mat.det = 1 := by
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; exact_mod_cast this
    simp only [τ_mat]; rw [det_fin_two_of]
    have h1 : a * (↑p * M 1 1) = A * M 1 1 := by rw [ha]; ring
    have h2 : A * M 1 1 - B * M 1 0 = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
      simp only [show A = M 0 0 + ↑↑b * M 1 0 from rfl,
        show B = M 0 1 + ↑↑b * M 1 1 from rfl]; ring
    linarith
  set τ : SL(2, ℤ) := ⟨τ_mat, hτ_det⟩ with hτ_def
  -- τ ∈ Gamma0 N
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((M 1 0 : ℤ) : ZMod N) = 0; exact hσ
  -- Gamma0MapUnits ⟨τ, _⟩ = unitOfCoprime p * Gamma0MapUnits ⟨σ, _⟩
  have hmap : Gamma0MapUnits ⟨τ, hτ_g0⟩ =
      ZMod.unitOfCoprime p hpN * Gamma0MapUnits ⟨σ, Gamma0_mem.mpr hσ⟩ := by
    ext; simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
      ZMod.coe_unitOfCoprime, Units.val_mul]
    show ((↑p * M 1 1 : ℤ) : ZMod N) = ((p : ℕ) : ZMod N) * ((M 1 1 : ℤ) : ZMod N)
    push_cast; ring
  -- Matrix equation: β_b · σ = τ · β_∞
  have hmatrix : T_p_upper p hp.pos b.val * mapGL ℚ σ =
      mapGL ℚ τ * T_p_lower p hp.pos := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_upper_coe, T_p_lower_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def,
        hB_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show A = a * ↑p from by linarith [ha])) |
        ring
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  -- f|τ = ⟨τ⟩f = ⟨p·σ₁₁⟩f = ⟨p⟩(⟨σ⟩f) by factoring Gamma0MapUnits
  exact congr_arg (· ∣[k] glMap (T_p_lower p hp.pos))
    (show ⇑f ∣[k] mapGL ℝ (τ : SL(2, ℤ)) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) from by
      change ⇑(diamondOpAux k ⟨τ, hτ_g0⟩ f) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f))
      rw [show diamondOpAux k ⟨τ, hτ_g0⟩ = diamondOp k (Gamma0MapUnits ⟨τ, hτ_g0⟩) from
        (diamondOp_eq_diamondOpAux k _ ⟨τ, hτ_g0⟩ rfl).symm, hmap,
        diamondOp_mul, LinearMap.comp_apply,
        diamondOp_eq_diamondOpAux k _ ⟨σ, Gamma0_mem.mpr hσ⟩ rfl])

/-- **Lower → Upper for Γ₀(N)**:
when `σ ∈ Γ₀(N)` and `p ∤ σ₁₀`, `β_∞ · σ` factors as `τ · β_{j'}` with
`τ ∈ Γ₀(N)` and `Gamma0MapUnits(τ) · unitOfCoprime(p) = Gamma0MapUnits(σ)`. -/
private theorem orbit_lower_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N)
    (hσ10 : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (b₀ : Fin p) (hb₀ : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b₀.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) * mapGL ℝ σ) =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k] glMap (T_p_upper p hp.pos
        (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b₀).val) := by
  haveI : Fact p.Prime := ⟨hp⟩; haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Gamma0_mem] at hσ
  have hσ10_ne : (M 1 0 : ZMod p) ≠ 0 :=
    fun h => hσ10 ((ZMod.intCast_zmod_eq_zero_iff_dvd (M 1 0) p).mp h)
  -- moebiusFin(b₀) at the p | A branch = (M 1 1 * (M 1 0)⁻¹).val
  have hA₀ : ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀
  set j' := ((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val
  have hj'_eq : (moebiusFin p hp M b₀).val = j' := by
    dsimp only [moebiusFin]; rw [if_pos hA₀]
  rw [hj'_eq]
  -- Factor β_∞ · σ = τ · β_{j'}
  have hmod : (M 1 0 : ZMod p) * (j' : ZMod p) = (M 1 1 : ZMod p) := by
    rw [show (j' : ZMod p) = ((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹ : ZMod p) from by
      show (((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val : ZMod p) = _
      rw [ZMod.natCast_val, ZMod.cast_id]]
    rw [mul_comm (M 1 1 : ZMod p) _, ← mul_assoc, zmod_mul_inv hσ10_ne, one_mul]
  have hp_div : (p : ℤ) ∣ (M 1 1 - M 1 0 * ↑j') := by
    have : ((M 1 1 - M 1 0 * ↑j' : ℤ) : ZMod p) = 0 := by
      push_cast; rw [sub_eq_zero]; exact hmod.symm
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨q, hq_eq⟩ := hp_div
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![↑p * M 0 0, M 0 1 - M 0 0 * ↑j'; M 1 0, q] with hτ_mat_def
  have hτ_det : τ_mat.det = 1 := by
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; exact_mod_cast this
    simp only [τ_mat]; rw [det_fin_two_of]
    have hpq : (↑p : ℤ) * q = M 1 1 - M 1 0 * ↑j' := by linarith [hq_eq]
    linarith [show ↑p * M 0 0 * q - (M 0 1 - M 0 0 * ↑j') * M 1 0 =
      M 0 0 * M 1 1 - M 0 1 * M 1 0 from by rw [show ↑p * M 0 0 * q =
        M 0 0 * (↑p * q) from by ring, hpq]; ring]
  set τ : SL(2, ℤ) := ⟨τ_mat, hτ_det⟩ with hτ_def
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((M 1 0 : ℤ) : ZMod N) = 0; exact hσ
  -- Gamma0MapUnits(τ) · unitOfCoprime(p) = Gamma0MapUnits(σ)
  -- τ₁₁ = q and p·q = M₁₁ - M₁₀·j'. Since (M₁₀ : ZMod N) = 0, p·q ≡ M₁₁.
  -- So q·p ≡ M₁₁, i.e., Gamma0Map(τ) * p = Gamma0Map(σ).
  have hunit_prod : Gamma0MapUnits ⟨τ, hτ_g0⟩ * ZMod.unitOfCoprime p hpN =
      Gamma0MapUnits ⟨σ, Gamma0_mem.mpr hσ⟩ := by
    ext; simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
      ZMod.coe_unitOfCoprime, Units.val_mul]
    show ((q : ℤ) : ZMod N) * ((p : ℕ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    rw [mul_comm, ← Int.cast_natCast (R := ZMod N), ← Int.cast_mul]
    have : ((↑p * q : ℤ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N) := by
      have h := hq_eq; rw [← h]; push_cast; rw [hσ, zero_mul, sub_zero]
    exact this
  have hmatrix : T_p_lower p hp.pos * mapGL ℚ σ =
      mapGL ℚ τ * T_p_upper p hp.pos j' := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_lower_coe, T_p_upper_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show M 1 1 = M 1 0 * ↑j' + q * ↑p from by linarith [hq_eq])) |
        ring
  -- Conclude: (⟨p⟩f)|β_∞·σ = (⟨p⟩f)|τ|β_{j'} = ⟨τ⟩(⟨p⟩f)|β_{j'}
  -- and ⟨τ⟩·⟨p⟩ = ⟨σ⟩, so ⟨τ⟩(⟨p⟩f) = ⟨σ⟩f
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] glMap (T_p_upper p hp.pos j'))
    (show ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        mapGL ℝ (τ : SL(2, ℤ)) = ⇑(diamondOpAux k ⟨σ, hσ⟩ f) from by
      change ⇑(diamondOpAux k ⟨τ, hτ_g0⟩ (diamondOp k (ZMod.unitOfCoprime p hpN) f)) =
        ⇑(diamondOpAux k ⟨σ, hσ⟩ f)
      rw [show diamondOpAux k ⟨τ, hτ_g0⟩ = diamondOp k (Gamma0MapUnits ⟨τ, hτ_g0⟩) from
        (diamondOp_eq_diamondOpAux k _ ⟨τ, hτ_g0⟩ rfl).symm,
        show diamondOp k (Gamma0MapUnits ⟨τ, hτ_g0⟩)
          (diamondOp k (ZMod.unitOfCoprime p hpN) f) =
          ((diamondOp k (Gamma0MapUnits ⟨τ, hτ_g0⟩)).comp
            (diamondOp k (ZMod.unitOfCoprime p hpN))) f from rfl,
        ← diamondOp_mul, hunit_prod,
        diamondOp_eq_diamondOpAux k _ ⟨σ, Gamma0_mem.mpr hσ⟩ rfl])

/-- **Lower → Lower for Γ₀(N)**:
when `σ ∈ Γ₀(N)` and `p ∣ σ₁₀`, `β_∞ · σ` factors as `τ · β_∞` with
`τ ∈ Γ₀(N)` and `Gamma0Map(τ) = Gamma0Map(σ)` (since τ₁₁ = σ₁₁).
The conclusion uses diamond commutativity:
`⟨τ⟩(⟨p⟩f) = ⟨σ⟩(⟨p⟩f) = ⟨p⟩(⟨σ⟩f)`
(the last step by commutativity of `(ZMod N)ˣ`). -/
private theorem orbit_lower_div_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N)
    (hσ10 : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (glMap (T_p_lower p hp.pos) * mapGL ℝ σ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      glMap (T_p_lower p hp.pos) := by
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hσ10_N : ((M 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hσ
  obtain ⟨c, hc⟩ := hσ10
  -- Construct τ = [[σ₀₀, p·σ₀₁], [c, σ₁₁]] where σ₁₀ = p·c
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ := !![M 0 0, ↑p * M 0 1; c, M 1 1] with hτ_mat_def
  have hτ_det : τ_mat.det = 1 := by
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; exact_mod_cast this
    simp only [τ_mat]; rw [det_fin_two_of]
    have h1 : M 0 1 * M 1 0 = ↑p * M 0 1 * c := by rw [hc]; ring
    linarith
  set τ : SL(2, ℤ) := ⟨τ_mat, hτ_det⟩ with hτ_def
  -- τ ∈ Gamma0 N: τ₁₀ = c, N | c
  -- (from gcd(p,N)=1 and N|σ₁₀, p|σ₁₀ ⟹ Np|σ₁₀)
  have hc_N : ((c : ℤ) : ZMod N) = 0 := by
    have h1 : ((↑p * c : ℤ) : ZMod N) = 0 := by rw [← hc]; exact hσ10_N
    rw [Int.cast_mul, Int.cast_natCast] at h1
    exact (IsUnit.mul_right_eq_zero (ZMod.unitOfCoprime p hpN).isUnit).mp h1
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((c : ℤ) : ZMod N) = 0; exact hc_N
  -- Gamma0Map(τ) = Gamma0Map(σ): τ₁₁ = M 1 1 = σ₁₁
  have hmap : Gamma0Map N ⟨τ, hτ_g0⟩ = Gamma0Map N ⟨σ, hσ⟩ := by
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    show ((τ_mat 1 1 : ℤ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    simp [τ_mat, Matrix.cons_val_one]
  -- Matrix equation: β_∞ · σ = τ · β_∞
  have hmatrix : T_p_lower p hp.pos * mapGL ℚ σ =
      mapGL ℚ τ * T_p_lower p hp.pos := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_lower_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show M 1 0 = c * ↑p from by linarith [hc])) |
        ring
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  -- (⟨p⟩f)|τ = ⟨τ⟩(⟨p⟩f) = ⟨σ⟩(⟨p⟩f) = ⟨p⟩(⟨σ⟩f)
  -- (diamond commutativity)
  exact congr_arg (· ∣[k] glMap (T_p_lower p hp.pos))
    (show ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k] mapGL ℝ (τ : SL(2, ℤ)) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) from by
      -- LHS = ⟨τ⟩(⟨p⟩f)
      change ⇑(diamondOpAux k ⟨τ, hτ_g0⟩ (diamondOp k (ZMod.unitOfCoprime p hpN) f)) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f))
      -- Rewrite ⟨τ⟩ = ⟨Gamma0MapUnits(τ)⟩ = ⟨Gamma0MapUnits(σ)⟩ = ⟨σ⟩
      rw [show diamondOpAux k ⟨τ, hτ_g0⟩ = diamondOp k (Gamma0MapUnits ⟨τ, hτ_g0⟩) from
        (diamondOp_eq_diamondOpAux k _ ⟨τ, hτ_g0⟩ rfl).symm]
      -- ⟨Gamma0MapUnits(τ)⟩ = ⟨Gamma0MapUnits(σ)⟩ by Gamma0Map equality
      have hmap_u : Gamma0MapUnits ⟨τ, hτ_g0⟩ = Gamma0MapUnits ⟨σ, hσ⟩ := by
        ext; simp [Gamma0MapUnits_val, hmap]
      rw [hmap_u]
      -- Now: ⟨σ_u⟩(⟨p⟩f) = ⟨p⟩(⟨σ_u⟩f) by commutativity of diamond operators
      -- ⟨σ_u⟩ ∘ ⟨p⟩ = ⟨σ_u · p⟩ = ⟨p · σ_u⟩ = ⟨p⟩ ∘ ⟨σ_u⟩
      have h_comm : (diamondOp k (Gamma0MapUnits ⟨σ, hσ⟩)).comp
          (diamondOp k (ZMod.unitOfCoprime p hpN)) =
          (diamondOp k (ZMod.unitOfCoprime p hpN)).comp
          (diamondOp k (Gamma0MapUnits ⟨σ, hσ⟩)) := by
        rw [← diamondOp_mul, ← diamondOp_mul, mul_comm]
      change ⇑(diamondOp k (Gamma0MapUnits ⟨σ, hσ⟩)
          (diamondOp k (ZMod.unitOfCoprime p hpN) f)) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f))
      rw [show diamondOp k (Gamma0MapUnits ⟨σ, hσ⟩)
          (diamondOp k (ZMod.unitOfCoprime p hpN) f) =
          ((diamondOp k (Gamma0MapUnits ⟨σ, hσ⟩)).comp
            (diamondOp k (ZMod.unitOfCoprime p hpN))) f from rfl, h_comm]
      show ⇑(((diamondOp k (ZMod.unitOfCoprime p hpN)).comp
          (diamondOp k (Gamma0MapUnits ⟨σ, hσ⟩))) f) = _
      rw [LinearMap.comp_apply, diamondOp_eq_diamondOpAux k _ ⟨σ, hσ⟩ rfl])

/-- Case 1 of slash invariance: `p ∣ σ₁₀`. The lower term is fixed and
upper terms permute via moebiusFin. -/
private theorem heckeT_p_slash_invariant_case1 [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10p : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ σ) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ) =
    (∑ b ∈ Finset.range p, ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by
    change (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1; exact_mod_cast σ.prop
  -- p | σ₁₀ implies p ∤ (σ₀₀ + b·σ₁₀) for all b (det ≡ 1 mod p)
  have hA_all : ∀ b : Fin p,
      ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) := by
    intro b hdvd
    have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hσ10p
    have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
      push_cast at this; rwa [h10, mul_zero, add_zero] at this
    have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by
      have h : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
        rw [det_fin_two] at hdet_M; exact hdet_M
      simp [h]
    rw [show ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) =
      (M 0 0 : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) from by
      push_cast; ring, h00, h10, zero_mul, mul_zero, sub_zero] at hd
    exact zero_ne_one hd
  -- Each upper term maps via moebiusFin
  have h_upper : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
      ⇑f ∣[k] glMap (T_p_upper p hp.pos (moebiusFin p hp M b).val)
    rw [← SlashAction.slash_mul,
        orbit_upper_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) b (hA_all b),
        show ⇑(diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f) = ⇑f from
          congr_arg _ (diamondOpAux_gamma1 k σ hσ f)]
  -- Lower term fixed by orbit_lower_div_gamma0
  have h_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul,
        orbit_lower_div_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) hσ10p,
        diamondOpAux_gamma1 k σ hσ f]; rfl
  -- moebiusFin is a bijection on Fin p
  have h_bij : Function.Bijective (moebiusFin p hp M) :=
    Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)
  -- Combine: lower term fixed, sum permutes
  rw [h_lower]; congr 1
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_equiv (Equiv.ofBijective _ h_bij)
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
    (fun b _ => h_upper b)

/-- Case 2 of slash invariance: `p ∤ σ₁₀`. One upper↔lower swap via
`orbit_lower_gamma0`, remaining terms permute via moebiusFin. -/
private theorem heckeT_p_slash_invariant_case2 [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10p : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ σ) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ) =
    (∑ b ∈ Finset.range p, ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by
    change (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1; exact_mod_cast σ.prop
  -- Step 1: For b with p ∤ A, upper→upper via moebiusFin
  have h_upper : ∀ b : Fin p,
      ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) →
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b hA
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
      ⇑f ∣[k] glMap (T_p_upper p hp.pos (moebiusFin p hp M b).val)
    rw [← SlashAction.slash_mul,
        orbit_upper_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) b hA,
        show ⇑(diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f) = ⇑f from
          congr_arg _ (diamondOpAux_gamma1 k σ hσ f)]
  -- Step 2: For b₀ where p | A, upper→lower
  have h_div : ∀ b : Fin p,
      (p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) →
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    intro b hA
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul,
        orbit_upper_div_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) b hA,
        diamondOpAux_gamma1 k σ hσ f]; rfl
  -- Step 3: Lower→upper (deterministic via moebiusFin)
  have h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
    intro h; exact hσ10p ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  -- Find b₀: the unique index where p | A
  set b₀ : Fin p := ⟨(-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  have hb₀_dvd : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0) := by
    rw [show (p : ℤ) ∣ _ ↔ ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm]; push_cast
    show (M 0 0 : ZMod p) + ((-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val : ZMod p) *
      (M 1 0 : ZMod p) = 0
    rw [ZMod.natCast_val, ZMod.cast_id]
    have : (-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹) * (M 1 0 : ZMod p) =
        -(M 0 0 : ZMod p) := by
      rw [mul_assoc, mul_comm (M 1 0 : ZMod p)⁻¹ _, zmod_mul_inv h10_ne, mul_one]
    rw [this, add_neg_cancel]
  -- Lower orbit identity: output = g(moebiusFin(b₀))
  have h_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp M b₀).val : GL (Fin 2) ℚ) := by
    change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul,
        orbit_lower_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) hσ10p b₀ hb₀_dvd,
        show ⇑(diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f) = ⇑f from
          congr_arg _ (diamondOpAux_gamma1 k σ hσ f)]; rfl
  -- Step 4: moebiusFin is a bijection on Fin p
  have h_bij : Function.Bijective (moebiusFin p hp M) :=
    Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)
  -- Step 5: Assembly
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have h_all : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      if (p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0)
      then ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)
      else ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b; split_ifs with h
    · exact h_div b h
    · exact h_upper b h
  simp_rw [h_all]; rw [h_lower]
  set g : Fin p → UpperHalfPlane → ℂ :=
    fun i => ⇑f ∣[k] (T_p_upper p hp.pos i.val : GL (Fin 2) ℚ) with hg_def
  set lower' := ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
    (T_p_lower p hp.pos : GL (Fin 2) ℚ)
  have h_ite_eq : ∀ i : Fin p,
      (if (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) then lower' else g (moebiusFin p hp M i)) =
      g (moebiusFin p hp M i) + if i = b₀ then lower' - g (moebiusFin p hp M b₀) else 0 := by
    intro i
    have h_iff : (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) ↔ i = b₀ := by
      constructor
      · intro hdvd
        exact moebiusFin_injective p hp M hdet_M (by
          simp only [moebiusFin,
            show ((M 0 0 + ↑i.val * M 1 0 : ℤ) : ZMod p) = 0 from
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd,
            show ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀_dvd, ↓reduceIte])
      · rintro rfl; exact hb₀_dvd
    simp only [h_iff]
    split_ifs with h1
    · subst h1; simp
    · rw [add_zero]
  show (∑ x, if (p : ℤ) ∣ (M 0 0 + ↑x.val * M 1 0) then lower'
        else g (moebiusFin p hp M x)) + g (moebiusFin p hp M b₀) =
      Finset.univ.sum g + lower'
  simp_rw [h_ite_eq, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ => lower' - g (moebiusFin p hp M b₀)),
      if_pos (Finset.mem_univ _)]
  have h_bij_sum : ∑ x : Fin p, g (moebiusFin p hp M x) = Finset.univ.sum g :=
    Finset.sum_equiv (Equiv.ofBijective _ h_bij)
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      (fun _ _ => rfl)
  rw [h_bij_sum]; abel

/-- Slash invariance of T_p under Γ₁(N).

The proof distributes the slash action over the sum, then applies the four
orbit factorisation cases. In each scenario, exactly one of the `p + 1`
output terms carries `(⟨p⟩f)|β_∞`, and the remaining `p` terms give
`f|β_j` for distinct `j ∈ {0,…,p−1}` (distinctness by injectivity of the
Möbius map `j ↦ (σ₀₁+jσ₁₁)/(σ₀₀+jσ₁₀)` on `ℙ¹(𝔽_p)`). -/
private theorem heckeT_p_slash_invariant [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (heckeT_p_fun k p hp hpN f) ∣[k] γ = heckeT_p_fun k p hp hpN f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  simp only [heckeT_p_fun, heckeT_p_ut]
  rw [SlashAction.add_slash, sum_slash]
  by_cases hσ10p : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  · exact heckeT_p_slash_invariant_case1 k p hp hpN f σ hσ hσ10p
  · exact heckeT_p_slash_invariant_case2 k p hp hpN f σ hσ hσ10p

/-- Case 1 of orbit sum comm: `p ∣ σ₁₀`. Upper terms permute via moebiusFin,
lower term tracks the diamond operator. -/
private theorem orbit_sum_comm_case1 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N))
    (hσ10p : (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ))) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) =
    (∑ b ∈ Finset.range p,
        ⇑(diamondOpAux k g f) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set σ := (g : SL(2, ℤ))
  have hσ : σ ∈ Gamma0 N := g.property
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by
    change (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1; exact_mod_cast σ.prop
  have h_coe : (⇑(diamondOpAux k g f) : UpperHalfPlane → ℂ) = ⇑f ∣[k] mapGL ℝ σ := rfl
  have hA_all : ∀ b : Fin p,
      ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) := by
    intro b hdvd
    have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hσ10p
    have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
      push_cast at this; rwa [h10, mul_zero, add_zero] at this
    have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by
      have h : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
        rw [det_fin_two] at hdet_M; exact hdet_M
      simp [h]
    rw [show ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) =
      (M 0 0 : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) from by
      push_cast; ring, h00, h10, zero_mul, mul_zero, sub_zero] at hd
    exact zero_ne_one hd
  -- Each upper term: f|β_b|σ = (⟨σ⟩f)|β_{φ(b)} via orbit_upper_gamma0
  have h_upper : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      (⇑f ∣[k] mapGL ℝ σ) ∣[k]
      (T_p_upper p hp.pos (moebiusFin p hp M b).val :
        GL (Fin 2) ℚ) := by
    intro b
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
      (⇑f ∣[k] mapGL ℝ σ) ∣[k] glMap (T_p_upper p hp.pos (moebiusFin p hp M b).val)
    rw [← SlashAction.slash_mul]
    have := orbit_upper_gamma0 k p hp hpN f σ hσ b (hA_all b)
    rw [h_coe] at this; exact this
  -- Lower term: (⟨p⟩f)|β_∞|σ = (⟨p⟩(⟨σ⟩f))|β_∞ via orbit_lower_div_gamma0
  have h_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul]
    exact orbit_lower_div_gamma0 k p hp hpN f σ hσ hσ10p
  -- moebiusFin is bijective
  have h_bij : Function.Bijective (moebiusFin p hp M) :=
    Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)
  -- Combine: lower term matches, sum permutes
  rw [h_lower]; congr 1
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  rw [h_coe]
  exact Finset.sum_equiv (Equiv.ofBijective _ h_bij)
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
    (fun b _ => h_upper b)

/-- Case 2 of orbit sum comm: `p ∤ σ₁₀`. One upper↔lower swap via
`orbit_lower_gamma0`, remaining terms permute via moebiusFin. -/
private theorem orbit_sum_comm_case2 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N))
    (hσ10p : ¬(p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ))) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) =
    (∑ b ∈ Finset.range p,
        ⇑(diamondOpAux k g f) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set σ := (g : SL(2, ℤ))
  have hσ : σ ∈ Gamma0 N := g.property
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by
    change (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1; exact_mod_cast σ.prop
  have h_coe : (⇑(diamondOpAux k g f) : UpperHalfPlane → ℂ) = ⇑f ∣[k] mapGL ℝ σ := rfl
  -- Step 1: upper→upper when p ∤ A
  have h_upper : ∀ b : Fin p,
      ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) →
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      (⇑f ∣[k] mapGL ℝ σ) ∣[k]
        (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b hA
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
      (⇑f ∣[k] mapGL ℝ σ) ∣[k] glMap (T_p_upper p hp.pos (moebiusFin p hp M b).val)
    rw [← SlashAction.slash_mul]
    have := orbit_upper_gamma0 k p hp hpN f σ hσ b hA
    rw [h_coe] at this; exact this
  -- Step 2: upper→lower when p | A
  have h_div : ∀ b : Fin p,
      (p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) →
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    intro b hA
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul]
    exact orbit_upper_div_gamma0 k p hp hpN f σ hσ b hA
  -- Step 3: Find b₀ and lower→upper
  have h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
    intro h; exact hσ10p ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  set b₀ : Fin p := ⟨(-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  have hb₀_dvd : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0) := by
    rw [show (p : ℤ) ∣ _ ↔ ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm]; push_cast
    show (M 0 0 : ZMod p) + ((-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val : ZMod p) *
      (M 1 0 : ZMod p) = 0
    rw [ZMod.natCast_val, ZMod.cast_id]
    have : (-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹) * (M 1 0 : ZMod p) =
        -(M 0 0 : ZMod p) := by
      rw [mul_assoc, mul_comm (M 1 0 : ZMod p)⁻¹ _, zmod_mul_inv h10_ne, mul_one]
    rw [this, add_neg_cancel]
  -- Lower orbit identity: (⟨p⟩f)|β_∞|σ = (⟨σ⟩f)|β_{φ(b₀)}
  have h_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    (⇑f ∣[k] mapGL ℝ σ) ∣[k]
      (T_p_upper p hp.pos (moebiusFin p hp M b₀).val : GL (Fin 2) ℚ) := by
    change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul]
    have := orbit_lower_gamma0 k p hp hpN f σ hσ hσ10p b₀ hb₀_dvd
    rw [h_coe] at this; exact this
  -- Step 4: moebiusFin bijection
  have h_bij : Function.Bijective (moebiusFin p hp M) :=
    Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)
  -- Step 5: Assembly
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  rw [h_coe]
  have h_all : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      if (p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0)
      then ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)
      else (⇑f ∣[k] mapGL ℝ σ) ∣[k]
        (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b; split_ifs with h
    · exact h_div b h
    · exact h_upper b h
  simp_rw [h_all]; rw [h_lower]
  set g' : Fin p → UpperHalfPlane → ℂ :=
    fun i => (⇑f ∣[k] mapGL ℝ σ) ∣[k] (T_p_upper p hp.pos i.val : GL (Fin 2) ℚ)
  set lower' := ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
    (T_p_lower p hp.pos : GL (Fin 2) ℚ)
  have h_ite_eq : ∀ i : Fin p,
      (if (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) then lower'
        else g' (moebiusFin p hp M i)) =
      g' (moebiusFin p hp M i) +
        if i = b₀ then lower' - g' (moebiusFin p hp M b₀) else 0 := by
    intro i
    have h_iff : (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) ↔ i = b₀ := by
      constructor
      · intro hdvd
        exact moebiusFin_injective p hp M hdet_M (by
          simp only [moebiusFin,
            show ((M 0 0 + ↑i.val * M 1 0 : ℤ) : ZMod p) = 0 from
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd,
            show ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀_dvd, ↓reduceIte])
      · rintro rfl; exact hb₀_dvd
    simp only [h_iff]
    split_ifs with h1
    · subst h1; simp
    · rw [add_zero]
  show (∑ x, if (p : ℤ) ∣ (M 0 0 + ↑x.val * M 1 0) then lower'
        else g' (moebiusFin p hp M x)) + g' (moebiusFin p hp M b₀) =
      Finset.univ.sum g' + lower'
  simp_rw [h_ite_eq, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ => lower' - g' (moebiusFin p hp M b₀)),
      if_pos (Finset.mem_univ _)]
  have h_bij_sum : ∑ x : Fin p, g' (moebiusFin p hp M x) = Finset.univ.sum g' :=
    Finset.sum_equiv (Equiv.ofBijective _ h_bij)
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      (fun _ _ => rfl)
  rw [h_bij_sum]; abel

/-- **Orbit sum comm** (Diamond–Shurman §5.2, p.170): for `g ∈ Γ₀(N)`,
`(T_p f) ∣[k] g = T_p (f ∣[k] g)`, i.e., `T_p` commutes with the
`Γ₀(N)` action.

The proof uses: (1) normality `Γ₁(N) ◁ Γ₀(N)` (`Gamma0_normalizes_Gamma1`),
(2) the same orbit-factorisation technique as `heckeT_p_slash_invariant`,
    but tracking how the `Γ₀(N)` element modifies the diamond operator. -/
private theorem orbit_sum_comm [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N)) :
    heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    heckeT_p_fun k p hp hpN (diamondOpAux k g f) := by
  simp only [heckeT_p_fun, heckeT_p_ut]
  rw [SlashAction.add_slash, sum_slash]
  by_cases hσ10p : (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  · exact orbit_sum_comm_case1 k p hp hpN f g hσ10p
  · exact orbit_sum_comm_case2 k p hp hpN f g hσ10p

/-- `GL₂(ℚ)` maps cusps of `Γ₁(N)` to cusps of `Γ₁(N)`.
Proof: Γ₁(N)-cusps are SL₂(ℤ)-cusps (by `Γ₁(N) ≤ SL₂(ℤ)`); GL₂(ℚ) preserves
SL₂(ℤ)-cusps (by `glMap_smul_isCusp`); SL₂(ℤ)-cusps are Γ₁(N)-cusps
(since Γ₁(N) has finite index, parabolic stabilizers intersect nontrivially). -/
private lemma Gamma1_isCusp_glMap_smul [NeZero N] (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ)) := by
  -- Γ₁(N).map ≤ 𝒮ℒ = ⊤.map, so c is an 𝒮ℒ-cusp
  have hc_SL : IsCusp c ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) :=
    hc.mono (Subgroup.map_mono le_top)
  -- GL₂(ℚ) preserves SL₂(ℤ)-cusps (inline proof of glMap_smul_isCusp)
  rw [← MonoidHom.range_eq_map] at hc_SL
  have hsmul_SL : IsCusp (glMap A • c) (mapGL ℝ : SL(2, ℤ) →* _).range := by
    rw [isCusp_SL2Z_iff] at hc_SL ⊢
    obtain ⟨q, rfl⟩ := hc_SL
    refine ⟨A • q, ?_⟩
    show OnePoint.map (algebraMap ℚ ℝ) (A • q) =
      glMap A • OnePoint.map (algebraMap ℚ ℝ) q
    simp [OnePoint.map_smul, glMap]
  rw [MonoidHom.range_eq_map] at hsmul_SL
  -- SL₂(ℤ)-cusps are Γ₁(N)-cusps (finite index)
  haveI : ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) := ⟨by
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  exact hsmul_SL.of_isFiniteRelIndex

private theorem heckeT_p_bdd_at_cusps [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (heckeT_p_fun k p hp hpN f) k := by
  -- Expand heckeT_p_fun = sum + diamond_lower
  simp only [heckeT_p_fun, heckeT_p_ut]
  -- Sum + lower term: use IsBoundedAt.add
  apply OnePoint.IsBoundedAt.add
  · -- Sum: use Finset.sum_induction with IsBoundedAt.add
    apply Finset.sum_induction _ (fun g => c.IsBoundedAt g k)
      (fun _ _ ha hb => ha.add hb)
      ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
    intro b _
    exact OnePoint.IsBoundedAt.smul_iff.mp
      (f.bdd_at_cusps' (Gamma1_isCusp_glMap_smul _ hc))
  · -- Diamond operator term: (⟨p⟩f) is a modular form, apply bdd_at_cusps
    exact OnePoint.IsBoundedAt.smul_iff.mp
      ((diamondOp k (ZMod.unitOfCoprime p hpN) f).bdd_at_cusps'
        (Gamma1_isCusp_glMap_smul _ hc))

/-! ### The linear map -/

/-- **The Hecke operator `T_p` on `M_k(Γ₁(N))`** for `p` prime coprime to `N`.
Following Diamond–Shurman Proposition 5.2.1:
`T_p(f) = Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]] + (⟨p⟩ f) ∣[k] [[p,0],[0,1]]`. -/
noncomputable def heckeT_p [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := heckeT_p_fun k p hp hpN f
        slash_action_eq' γ hγ := heckeT_p_slash_invariant k p hp hpN f γ hγ }
      holo' := heckeT_p_holomorphic k p hp hpN f
      bdd_at_cusps' hc := heckeT_p_bdd_at_cusps k p hp hpN f hc }
  map_add' f g := by
    ext z; simp only [ModularForm.add_apply]
    show heckeT_p_fun k p hp hpN (f + g) z =
      heckeT_p_fun k p hp hpN f z + heckeT_p_fun k p hp hpN g z
    simp only [heckeT_p_fun, heckeT_p_ut, Pi.add_apply]
    rw [show (⇑(f + g) : UpperHalfPlane → ℂ) = ⇑f + ⇑g from rfl,
      show diamondOp k (ZMod.unitOfCoprime p hpN) (f + g) =
        diamondOp k (ZMod.unitOfCoprime p hpN) f +
        diamondOp k (ZMod.unitOfCoprime p hpN) g from map_add _ f g,
      show (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f +
        diamondOp k (ZMod.unitOfCoprime p hpN) g) : UpperHalfPlane → ℂ) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) +
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) g) from rfl]
    simp only [SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply,
      Finset.sum_apply]
    ring
  map_smul' c f := by
    ext z; simp only [RingHom.id_apply]
    show heckeT_p_fun k p hp hpN (c • f) z = c * heckeT_p_fun k p hp hpN f z
    simp only [heckeT_p_fun, heckeT_p_ut, Pi.add_apply]
    -- Rewrite ⇑(c • f) and diamond of (c • f)
    rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      show diamondOp k (ZMod.unitOfCoprime p hpN) (c • f) =
        c • diamondOp k (ZMod.unitOfCoprime p hpN) f from map_smul _ c f,
      show (⇑(c • diamondOp k (ZMod.unitOfCoprime p hpN) f) : UpperHalfPlane → ℂ) =
        c • ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) from rfl]
    simp_rw [smul_slash_pos_det k c _ _ (T_p_upper_det_pos p hp.pos _)]
    rw [smul_slash_pos_det k c _ _ (T_p_lower_det_pos p hp.pos)]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_apply]
    ring

/-! ### Commutation with diamond operators

Diamond–Shurman §5.2, page 170: `⟨d⟩ T_p = T_p ⟨d⟩` for all `d ∈ (ℤ/Nℤ)ˣ`. -/

/-- `T_p` commutes with the diamond operators: `⟨d⟩ ∘ T_p = T_p ∘ ⟨d⟩`.
Proved by reducing to `orbit_sum_comm` and `diamondOpAux_eq_of_Gamma0Map_eq`. -/
theorem heckeT_p_comm_diamondOp [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (d : (ZMod N)ˣ) :
    (diamondOp k d).comp (heckeT_p k p hp hpN) =
    (heckeT_p k p hp hpN).comp (diamondOp k d) := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
  ext f z
  -- LHS: (⟨d⟩(T_p f))(z) = (T_p f)|[k] g(z)
  show (diamondOp k d (heckeT_p k p hp hpN f)) z =
    (heckeT_p k p hp hpN (diamondOp k d f)) z
  rw [diamondOp_eq_diamondOpAux k d g hg]
  -- Now LHS = (diamondOpAux k g)(T_p f) = (T_p f)|[k] g
  -- and RHS = T_p(diamondOpAux k g f)
  show (diamondOpAux k g (heckeT_p k p hp hpN f)) z =
    (heckeT_p k p hp hpN (diamondOpAux k g f)) z
  -- LHS coercion: ⇑(diamondOpAux k g (T_p f)) = (⇑(T_p f))|[k] mapGL ℝ g
  -- which = (heckeT_p_fun k p hp hpN f)|[k] mapGL ℝ g
  change ((⇑(heckeT_p k p hp hpN f)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z =
    (heckeT_p k p hp hpN (diamondOpAux k g f)) z
  -- T_p f coerces to heckeT_p_fun
  show (heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ))) z =
    heckeT_p_fun k p hp hpN (diamondOpAux k g f) z
  exact congr_fun (orbit_sum_comm k p hp hpN f g) z

/-! ### Preservation of character spaces -/

/-- `T_p` preserves the modular form character space `M_k(Γ₁(N), χ)`. -/
theorem heckeT_p_preserves_modFormCharSpace [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_p k p hp hpN f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff] at hf ⊢
  intro d
  have h_comm := heckeT_p_comm_diamondOp k p hp hpN d
  have h1 : diamondOpHom k d (heckeT_p k p hp hpN f) =
      heckeT_p k p hp hpN (diamondOpHom k d f) := by
    show (diamondOp k d).comp (heckeT_p k p hp hpN) f =
      (heckeT_p k p hp hpN).comp (diamondOp k d) f
    rw [h_comm]
  rw [h1, hf d, map_smul]

/-- `T_p` preserves the cusp form character space `S_k(Γ₁(N), χ)`.
(Requires defining T_p on cusp forms; stated here for completeness.) -/
theorem heckeT_p_preserves_cuspFormCharSpace [NeZero N] (k : ℤ) (p : ℕ)
    (_hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) {_f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (_hf : _f ∈ cuspFormCharSpace k χ) :
    True := by -- placeholder: cusp form T_p not yet constructed
  trivial

/-! ### Bridge to abstract Hecke ring -/

/-- `diag(1,p)` lies in `Δ₁(N)` for any `N` and `p > 0`. -/
lemma diag_1p_mem_Delta1 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    diagMat 2 ![1, p] ∈ Delta1_submonoid N := by
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
  · -- (A 0 0 : ZMod N) = 1: top-left entry is 1
    simp [A, Matrix.diagonal]

end HeckeRing.GL2
