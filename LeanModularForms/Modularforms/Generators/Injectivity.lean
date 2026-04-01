module

public import LeanModularForms.Modularforms.Generators.Surjectivity

/-!
# Generators of the graded ring of level 1 modular forms: Injectivity and main results

The proof decomposes a polynomial into its weighted-homogeneous components
(with respect to the weight function `![4, 6]`), shows each component maps
independently to a single graded piece of the direct sum, and establishes
per-weight injectivity by strong induction on the weight. The main results are
the algebra isomorphism `modularFormsEquivMvPolynomial` and the generation
theorem `E₄E₆_generate`.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

private lemma evalE₄E₆_mono_grade (a b : ℕ) (k : ℤ)
    (hk : k ≠ (↑a * 4 + ↑b * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) k = 0 := by
  rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1,
    DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_ne _ _ _ (by omega)

private lemma monomial_fin2_eq (d : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial d c =
    MvPolynomial.C c * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq, mul_assoc]; congr 1
  rw [Finsupp.prod, Finset.prod_subset (fun _ _ => Finset.mem_univ _) (fun i _ hi => by
    have : d i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi
    rw [this, pow_zero])]
  simp only [Fin.prod_univ_two]

private lemma evalE₄E₆_monomial_grade (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ (↑(d 0) * 4 + ↑(d 1) * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.monomial d c)) k = 0 := by
  rw [monomial_fin2_eq, show MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
    MvPolynomial.X (1 : Fin 2) ^ d 1 =
    MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1)
    from mul_assoc _ _ _]
  rw [map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    DirectSum.smul_apply, evalE₄E₆_mono_grade (d 0) (d 1) k hk, smul_zero]

private lemma weight_fin2_cast (d : Fin 2 →₀ ℕ) :
    (Finsupp.weight E₄E₆Weight d : ℤ) = ↑(d 0) * 4 + ↑(d 1) * 6 := by
  have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
    change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
    simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
    rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp only [zero_smul])]
    simp only [Fin.sum_univ_two, E₄E₆Weight, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_comm, smul_eq_mul]
  rw [this]; push_cast; ring

private lemma evalE₄E₆_whc_grade (n : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n) (k : ℤ) (hk : k ≠ ↑n) :
    (evalE₄E₆ p) k = 0 := by
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, DFinsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply evalE₄E₆_monomial_grade
  intro heq; apply hk
  rw [heq, ← weight_fin2_cast d, hp (MvPolynomial.mem_support_iff.mp hd)]

private lemma evalE₄E₆_component_eq (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    (evalE₄E₆ (MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p)) (↑n : ℤ) =
    (evalE₄E₆ p) (↑n : ℤ) := by
  have hdecomp : p = MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p +
    (p - MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p) := by ring
  set q := p - MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p
  conv_rhs => rw [hdecomp, map_add, DFinsupp.add_apply]
  suffices h : (evalE₄E₆ q) (↑n : ℤ) = 0 by rw [h, add_zero]
  rw [← MvPolynomial.support_sum_monomial_coeff q, map_sum, DFinsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply evalE₄E₆_monomial_grade
  intro heq
  have : Finsupp.weight E₄E₆Weight d = n := by
    have := weight_fin2_cast d; omega
  exfalso; exact (MvPolynomial.mem_support_iff.mp hd) (by
    simp only [q, MvPolynomial.coeff_sub]
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos this, sub_self])

private lemma no_wt_monomial_of_odd {n : ℕ} (hn : Odd n) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weight d ≠ n := by
  intro h
  have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
    have := weight_fin2_cast d; omega
  rw [this] at h
  have hev : Even n := ⟨d 0 * 2 + d 1 * 3, by omega⟩
  simp only [Nat.even_iff, Nat.odd_iff] at hev hn; omega

private lemma no_wt_monomial_of_two (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weight d ≠ 2 := by
  intro h
  have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
    have := weight_fin2_cast d; omega
  rw [this] at h; omega

private lemma whomog_eq_zero_of_no_monomials {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (hno : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight E₄E₆Weight d ≠ n) : p = 0 := by
  rw [← MvPolynomial.support_eq_empty]
  by_contra h
  obtain ⟨d, hd⟩ := Finset.nonempty_of_ne_empty h
  exact hno d (hp (MvPolynomial.mem_support_iff.mp hd))

private lemma weight_eq_4a_6b (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
  change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
  simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
  rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp only [zero_smul])]
  simp only [Fin.sum_univ_two, E₄E₆Weight, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_comm, smul_eq_mul]

private lemma finsupp_of_fin2 (a b : ℕ) :
    ∃ d : Fin 2 →₀ ℕ, d 0 = a ∧ d 1 = b := by
  exact ⟨Finsupp.equivFunOnFinite.invFun ![a, b], by dsimp, by dsimp⟩

private lemma whomog_unique_monomial {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (d₀ : Fin 2 →₀ ℕ) (hd₀ : Finsupp.weight E₄E₆Weight d₀ = n)
    (huniq : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight E₄E₆Weight d = n → d = d₀) :
    p = MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ p) := by
  ext d
  by_cases hd : d = d₀
  · subst hd; simp only [MvPolynomial.coeff_monomial, ↓reduceIte]
  · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hd)]
    exact hp.coeff_eq_zero d (fun h => hd (huniq d h))

private lemma per_weight_injective_unique_monomial {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (d₀ : Fin 2 →₀ ℕ) (hd₀ : Finsupp.weight E₄E₆Weight d₀ = n)
    (huniq : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight E₄E₆Weight d = n → d = d₀)
    (hmf_ne : ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ (d₀ 0) *
      (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ (d₀ 1))
      (↑n : ℤ) ≠ 0) : p = 0 := by
  have hpc := whomog_unique_monomial p hp d₀ hd₀ huniq
  rw [hpc] at heval ⊢
  rw [monomial_fin2_eq, show MvPolynomial.C (MvPolynomial.coeff d₀ p) *
    MvPolynomial.X (0 : Fin 2) ^ d₀ 0 * MvPolynomial.X (1 : Fin 2) ^ d₀ 1 =
    MvPolynomial.C (MvPolynomial.coeff d₀ p) *
    (MvPolynomial.X (0 : Fin 2) ^ d₀ 0 * MvPolynomial.X (1 : Fin 2) ^ d₀ 1)
    from mul_assoc _ _ _] at heval
  rw [map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1,
    DirectSum.smul_apply] at heval
  rcases smul_eq_zero.mp heval with hc | hmz
  · rw [show MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ p) =
      MvPolynomial.monomial d₀ 0 from by rw [hc], MvPolynomial.monomial_zero]
  · exact absurd hmz hmf_ne

private lemma X0_cubed_eq : (MvPolynomial.X (0 : Fin 2)) ^ 3 =
    (MvPolynomial.X (1 : Fin 2)) ^ 2 + (1728 : ℂ) • Delta_poly := by
  simp only [Delta_poly, smul_smul]
  norm_num

private lemma Delta_poly_isWeightedHomogeneous :
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight Delta_poly 12 := by
  unfold Delta_poly
  simp only [MvPolynomial.smul_eq_C_mul]
  intro d hd
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sub] at hd
  by_cases hd3 : MvPolynomial.coeff d
      (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ) ≠ 0
  · exact ((MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (0 : Fin 2)).pow 3) hd3
  · push_neg at hd3
    by_cases hd6 : MvPolynomial.coeff d
        (MvPolynomial.X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℂ) ≠ 0
    · exact ((MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (1 : Fin 2)).pow 2) hd6
    · push_neg at hd6; simp only [hd3, hd6, sub_self, mul_zero, ne_eq, not_true] at hd

private lemma mul_Delta_map_injective {k : ℤ} (f : ModularForm Γ(1) (k - 12))
    (hf : mul_Delta_map k f = 0) : f = 0 := by
  ext z
  have hz := congr_fun (congr_arg (fun x => x.toFun) hf) z
  simp only [ModularForm.zero_apply, SlashInvariantForm.toFun_eq_coe,
    ModularForm.toSlashInvariantForm_coe] at hz
  rw [mul_Delta_map_eq] at hz
  exact (mul_eq_zero.mp hz).resolve_right (Δ_ne_zero z)

private lemma monomial_reduction (a b : ℕ) (ha : 3 ≤ a) :
    (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X (1 : Fin 2) ^ b : MvPolynomial (Fin 2) ℂ) =
    MvPolynomial.X 0 ^ (a - 3) * MvPolynomial.X 1 ^ (b + 2) +
    (1728 : ℂ) • Delta_poly * (MvPolynomial.X 0 ^ (a - 3) * MvPolynomial.X 1 ^ b) := by
  have : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ a =
    MvPolynomial.X 0 ^ (a - 3) * MvPolynomial.X (0 : Fin 2) ^ 3 := by
    rw [← pow_add]; congr 1; omega
  rw [this, X0_cubed_eq]
  ring

private lemma X0_pow_mul_X1_pow_isWeightedHomogeneous (a b n : ℕ) (hab : a * 4 + b * 6 = n) :
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight
      (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X (1 : Fin 2) ^ b :
        MvPolynomial (Fin 2) ℂ) n := by
  convert ((MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (0 : Fin 2)).pow a).mul
    ((MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (1 : Fin 2)).pow b) using 1
  simp only [E₄E₆Weight, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]; omega

private lemma delta_piece_isWeightedHomogeneous {n : ℕ} (hn12 : 12 ≤ n)
    (d : Fin 2 →₀ ℕ) (hd_ge : 3 ≤ d 0) (hwd : d 0 * 4 + d 1 * 6 = n) (c : ℂ) :
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight
      (MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
          MvPolynomial.X (1 : Fin 2) ^ (d 1)))) n := by
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  rw [MvPolynomial.smul_eq_C_mul,
    show MvPolynomial.C (1728 : ℂ) * Delta_poly *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
      MvPolynomial.C (1728 : ℂ) * (Delta_poly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
          MvPolynomial.X (1 : Fin 2) ^ d 1)) from by ring]
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  convert Delta_poly_isWeightedHomogeneous.mul
    (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by omega))
    using 1; omega

private lemma delta_piece_eq_monomial_sub
    (d : Fin 2 →₀ ℕ) (hd_ge : 3 ≤ d 0) (c : ℂ)
    (d' : Fin 2 →₀ ℕ) (hd' : d' = Finsupp.single (0 : Fin 2) (d 0 - 3) +
      Finsupp.single (1 : Fin 2) (d 1 + 2)) :
    MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ (d 1))) =
    (MvPolynomial.monomial d) c - (MvPolynomial.monomial d') c := by
  subst hd'
  have h1728 : (1728 : ℂ) • Delta_poly =
    MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2 := by
    simp only [Delta_poly, smul_smul]; norm_num
  have hd_fin : d = Finsupp.single (0 : Fin 2) (d 0) +
      Finsupp.single (1 : Fin 2) (d 1) := by
    ext i; fin_cases i <;> simp [Finsupp.add_apply]
  have hdp_simp : MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ (d 1))) =
    MvPolynomial.C c *
      (MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2) *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
        MvPolynomial.X (1 : Fin 2) ^ (d 1)) := by
    rw [h1728]; ring
  rw [hdp_simp]
  have h3 : (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ) *
    (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
    MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1 := by
    have h := show (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 3 *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)
      = (MvPolynomial.X (0 : Fin 2) ^ 3 * MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3)) *
          MvPolynomial.X (1 : Fin 2) ^ d 1 from by ring
    rw [h, ← pow_add, show 3 + (d 0 - 3) = d 0 from by omega]
  have h2 : (MvPolynomial.X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℂ) *
    (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
    MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
      MvPolynomial.X (1 : Fin 2) ^ (d 1 + 2) := by
    have h := show (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 2 *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)
      = MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
          (MvPolynomial.X (1 : Fin 2) ^ d 1 * MvPolynomial.X (1 : Fin 2) ^ 2) from by ring
    rw [h, ← pow_add]
  rw [show MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ 3 -
      MvPolynomial.X (1 : Fin 2) ^ 2) *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
        MvPolynomial.X (1 : Fin 2) ^ d 1) =
    MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ 3 *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)) -
    MvPolynomial.C c * (MvPolynomial.X (1 : Fin 2) ^ 2 *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
        MvPolynomial.X (1 : Fin 2) ^ d 1)) from by ring,
    h3, h2]
  congr 1
  · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul, MvPolynomial.C_mul_monomial, mul_one]
    exact congrArg (· c) (congrArg MvPolynomial.monomial hd_fin.symm)
  · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul, MvPolynomial.C_mul_monomial, mul_one]

private lemma Finset.sum_lt_sum_of_replace {α : Type*} [DecidableEq α]
    (S S' : Finset α) (f : α → ℕ) (d d' : α)
    (hd_mem : d ∈ S) (hd_not : d ∉ S')
    (hS' : S' ⊆ S.erase d ∪ {d'})
    (hlt : f d' < f d) :
    ∑ x ∈ S', f x < ∑ x ∈ S, f x := by
  by_cases hd'S : d' ∈ S
  · calc ∑ x ∈ S', f x
        ≤ ∑ x ∈ S.erase d, f x := Finset.sum_le_sum_of_subset (fun x hx =>
          Finset.mem_erase.mpr ⟨fun h => hd_not (h ▸ hx),
            match Finset.mem_union.mp (hS' hx) with
            | .inl h => Finset.mem_of_mem_erase h
            | .inr h => Finset.mem_singleton.mp h ▸ hd'S⟩)
      _ < ∑ x ∈ S.erase d, f x + f d :=
          Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (by omega))
      _ = ∑ x ∈ S, f x := Finset.sum_erase_add S f hd_mem
  · calc ∑ x ∈ S', f x
        ≤ ∑ x ∈ S.erase d ∪ {d'}, f x := Finset.sum_le_sum_of_subset hS'
      _ = ∑ x ∈ S.erase d, f x + f d' := by
          rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr
            (fun h => hd'S (Finset.mem_of_mem_erase h))), Finset.sum_singleton]
      _ < ∑ x ∈ S.erase d, f x + f d := Nat.add_lt_add_left hlt _
      _ = ∑ x ∈ S, f x := Finset.sum_erase_add S f hd_mem

open Classical in
private lemma mvpoly_support_after_reduction {σ R : Type*} [CommRing R] [DecidableEq σ]
    (p : MvPolynomial σ R) (d d' : σ →₀ ℕ) (c : R)
    (hdd' : d ≠ d') (hc : MvPolynomial.coeff d p = c) :
    let delta := MvPolynomial.monomial d c - MvPolynomial.monomial d' c
    d ∉ (p - delta).support ∧ (p - delta).support ⊆ p.support.erase d ∪ {d'} := by
  have hcoeff_d : MvPolynomial.coeff d
      (p - (MvPolynomial.monomial d c - MvPolynomial.monomial d' c)) = 0 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
      if_pos rfl, if_neg hdd'.symm, sub_zero, hc, sub_self]
  have hd_not : d ∉ (p - (MvPolynomial.monomial d c -
      MvPolynomial.monomial d' c)).support :=
    MvPolynomial.notMem_support_iff.mpr hcoeff_d
  refine ⟨hd_not, fun x hx => ?_⟩
  rcases Finset.mem_union.mp (MvPolynomial.support_sub σ p _ hx) with hp | hdelta
  · by_cases hxd : x = d
    · exact absurd (hxd ▸ hx) hd_not
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxd, hp⟩)
  · rcases Finset.mem_union.mp (MvPolynomial.support_sub σ _ _ hdelta) with h1 | h2
    · rw [MvPolynomial.support_monomial] at h1
      split_ifs at h1
      · exact absurd h1 (Finset.notMem_empty _)
      · exact absurd ((Finset.mem_singleton.mp h1) ▸ hx) hd_not
    · rw [MvPolynomial.support_monomial] at h2
      split_ifs at h2
      · exact absurd h2 (Finset.notMem_empty _)
      · exact Finset.mem_union_right _ (by rwa [Finset.mem_singleton] at h2 ⊢)

private lemma whomog_poly_Delta_decomp {n : ℕ} (hn12 : 12 ≤ n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n) :
    ∃ r s : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n ∧
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12) ∧
      p = r + Delta_poly * s ∧
      (∀ d ∈ r.support, d 0 < 3) := by
  suffices key : ∀ (M : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n →
      (∑ d ∈ p.support, d 0) ≤ M →
      ∃ r s : MvPolynomial (Fin 2) ℂ,
        MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n ∧
        MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12) ∧
        p = r + Delta_poly * s ∧
        (∀ d ∈ r.support, d 0 < 3) from
    key _ p hp le_rfl
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro p hp hM
  by_cases hall : ∀ d ∈ p.support, d 0 < 3
  · exact ⟨p, 0, hp, MvPolynomial.isWeightedHomogeneous_zero ℂ E₄E₆Weight (n - 12),
      by simp only [mul_zero, add_zero], hall⟩
  · push_neg at hall
    obtain ⟨d, hd_mem, hd_ge⟩ := hall
    have hwd : d 0 * 4 + d 1 * 6 = n := by
      have := hp (MvPolynomial.mem_support_iff.mp hd_mem)
      have := weight_eq_4a_6b d; omega
    set c := MvPolynomial.coeff d p
    set delta_piece := MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ (d 1)))
    set p' := p - delta_piece with hp'_def
    have hp_eq : p = p' + delta_piece := by simp only [p', sub_add_cancel]
    have hp'_wh : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p' n := by
      rw [hp'_def]
      exact (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ E₄E₆Weight n _).mp
        (Submodule.sub_mem _
          ((MvPolynomial.mem_weightedHomogeneousSubmodule ℂ E₄E₆Weight n p).mpr hp)
          ((MvPolynomial.mem_weightedHomogeneousSubmodule ℂ E₄E₆Weight n
            delta_piece).mpr (delta_piece_isWeightedHomogeneous hn12 d hd_ge hwd c)))
    set q₁ := MvPolynomial.C (c * 1728) *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ (d 1))
    have hdelta_eq : delta_piece = Delta_poly * q₁ := by
      simp only [delta_piece, q₁, MvPolynomial.smul_eq_C_mul, map_mul]; ring
    have hM_lt : ∑ d' ∈ p'.support, d' 0 < ∑ d' ∈ p.support, d' 0 := by
      set d' := Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)
        with hd'_def
      have hdd' : d ≠ d' := by
        intro heq; have h0 := Finsupp.ext_iff.mp heq (0 : Fin 2)
        simp only [Fin.isValue, hd'_def, Finsupp.add_apply, Finsupp.single_eq_same,
          ne_eq, zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne, add_zero] at h0
        omega
      have hdp_mono : delta_piece =
          (MvPolynomial.monomial d) c - (MvPolynomial.monomial d') c :=
        delta_piece_eq_monomial_sub d hd_ge c d' hd'_def
      obtain ⟨hd_not, hsupp⟩ := hdp_mono ▸ mvpoly_support_after_reduction p d d' c hdd' rfl
      exact Finset.sum_lt_sum_of_replace p.support p'.support
        (· 0) d d' hd_mem hd_not hsupp (by simp [hd'_def, Finsupp.add_apply]; omega)
    obtain ⟨r, s', hr_wh, hs'_wh, hp'_eq, hr_red⟩ :=
      ih (∑ d' ∈ p'.support, d' 0) (by omega) p' hp'_wh le_rfl
    refine ⟨r, s' + q₁, hr_wh, hs'_wh.add (.C_mul
      (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by omega)) _), ?_,
      hr_red⟩
    rw [hp_eq, hdelta_eq, hp'_eq, mul_add]; ring

private lemma unique_small_weight_soln {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : a₁ < 3) (ha₂ : a₂ < 3)
    (h : a₁ * 4 + b₁ * 6 = a₂ * 4 + b₂ * 6) : a₁ = a₂ ∧ b₁ = b₂ := by
  exact ⟨by interval_cases a₁ <;> interval_cases a₂ <;> omega, by omega⟩

private lemma reduced_poly_is_scalar {n : ℕ} (_hn12 : 12 ≤ n)
    (r : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) :
    ∀ d₁ d₂ : Fin 2 →₀ ℕ,
      d₁ ∈ r.support → d₂ ∈ r.support → d₁ = d₂ := by
  intro d₁ d₂ hd₁ hd₂
  have hw1 := hr (MvPolynomial.mem_support_iff.mp hd₁)
  have hw2 := hr (MvPolynomial.mem_support_iff.mp hd₂)
  have h46_1 := weight_eq_4a_6b d₁; rw [hw1] at h46_1
  have h46_2 := weight_eq_4a_6b d₂; rw [hw2] at h46_2
  have heq : d₁ 0 * 4 + d₁ 1 * 6 = d₂ 0 * 4 + d₂ 1 * 6 := by linarith
  obtain ⟨hd0, hd1⟩ := unique_small_weight_soln (hr_red d₁ hd₁) (hr_red d₂ hd₂) heq
  ext i; fin_cases i <;> assumption

private lemma evalE₄E₆_Delta_mul_coeff_zero {n : ℕ} (_hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12)) :
    (qExpansion 1 ↑((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 := by
  rw [map_mul, evalE₄E₆_whc_eq_single 12 Delta_poly Delta_poly_isWeightedHomogeneous,
    evalE₄E₆_whc_eq_single (n - 12) s hs, DirectSum.of_mul_of]
  set D := evalE₄E₆ Delta_poly; set S := evalE₄E₆ s
  simp only [Nat.cast_ofNat] at *
  have hcast : (12 : ℤ) + ↑(n - 12) = ↑n := by omega
  rw [DirectSum.of_apply, dif_pos hcast]
  have hq_eq : qExpansion 1 ↑(hcast ▸ GradedMonoid.GMul.mul (D 12) (S (↑(n-12))) :
      ModularForm Γ(1) (↑n)) =
      qExpansion 1 ↑(GradedMonoid.GMul.mul (D 12) (S (↑(n-12)))) := by
    congr 1; ext z
    have : ∀ {k₁ k₂ : ℤ} (heq : k₁ = k₂) (f : ModularForm Γ(1) k₁) (z : ℍ),
      (heq ▸ f : ModularForm Γ(1) k₂) z = f z := by intros; subst_vars; rfl
    exact this hcast _ z
  rw [hq_eq, show (↑(GradedMonoid.GMul.mul (D 12) (S (↑(n-12)))) : ℍ → ℂ) =
      ↑((D 12).mul (S (↑(n-12)))) from rfl]
  have hmul_coeff := qExpansion_mul_coeff 1 12 (↑(n-12)) (D 12) (S (↑(n-12)))
  simp only [Nat.cast_one] at hmul_coeff; rw [hmul_coeff]
  simp only [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton]
  rw [show D 12 = ModForm_mk Γ(1) 12 Delta from evalE₄E₆_Delta_poly_grade,
    qExpansion_coeff_zero_Delta, zero_mul]

private lemma coeff_zero_of_eval_zero {n : ℕ} (hn12 : 12 ≤ n)
    (r s : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n)
    (hs : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12))
    (hr_red : ∀ d ∈ r.support, d 0 < 3)
    (heval : (evalE₄E₆ (r + Delta_poly * s)) (↑n : ℤ) = 0) :
    r = 0 := by
  by_cases hr_empty : r.support = ∅
  · rwa [MvPolynomial.support_eq_empty] at hr_empty
  · obtain ⟨d₀, hd₀⟩ := Finset.nonempty_of_ne_empty hr_empty
    have hr_mono : r = MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ r) := by
      ext d
      by_cases hd : d = d₀
      · subst hd; simp only [MvPolynomial.coeff_monomial, ↓reduceIte]
      · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hd)]
        by_cases hd_supp : d ∈ r.support
        · exact absurd (reduced_poly_is_scalar hn12 r hr hr_red d d₀ hd_supp hd₀) hd
        · rwa [MvPolynomial.mem_support_iff, not_not] at hd_supp
    have hwd₀ := hr (MvPolynomial.mem_support_iff.mp hd₀)
    have hwd₀' := weight_eq_4a_6b d₀; rw [hwd₀] at hwd₀'
    set c := MvPolynomial.coeff d₀ r
    suffices hc : c = 0 by rw [hr_mono, hc, MvPolynomial.monomial_zero]
    set Q := qExpansionAddHom (show (0 : ℝ) < (1 : ℝ) by norm_num)
      (show (1 : ℝ) ∈ Γ(1).strictPeriods from by simp) (↑n)
    have hQ_zero : Q ((evalE₄E₆ (r + Delta_poly * s)) (↑n : ℤ)) = 0 := by
      rw [heval]; exact map_zero Q
    rw [show evalE₄E₆ (r + Delta_poly * s) = evalE₄E₆ r + evalE₄E₆ (Delta_poly * s)
      from map_add _ _ _, DFinsupp.add_apply, map_add] at hQ_zero
    have hcoeff_sum : (Q ((evalE₄E₆ r) (↑n : ℤ))).coeff 0 +
        (Q ((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 := by
      rw [← PowerSeries.coeff_add, hQ_zero, map_zero]
    change (qExpansion 1 ↑((evalE₄E₆ r) (↑n : ℤ))).coeff 0 +
      (qExpansion 1 ↑((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 at hcoeff_sum
    set mo := ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ d₀ 0 *
      (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ d₀ 1)
    have hq_r : (qExpansion 1 ↑((evalE₄E₆ r) (↑n : ℤ))).coeff 0 = c := by
      rw [hr_mono, monomial_fin2_eq,
        show MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d₀ 0 *
          MvPolynomial.X (1 : Fin 2) ^ d₀ 1 =
          MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ d₀ 0 *
          MvPolynomial.X (1 : Fin 2) ^ d₀ 1) from mul_assoc _ _ _,
        map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]
      rw [DirectSum.smul_apply,
        show (↑(c • mo (↑n : ℤ)) : ℍ → ℂ) = c • ↑(mo (↑n : ℤ)) from rfl,
        qExpansion_smul (show (0 : ℝ) < 1 from by norm_num)
          (show (1 : ℝ) ∈ Γ(1).strictPeriods from by simp) c (mo (↑n : ℤ)),
        PowerSeries.coeff_smul, monomial_coeff_zero_eq_one n (d₀ 0) (d₀ 1) (by omega),
        smul_eq_mul, mul_one]
    rw [hq_r, evalE₄E₆_Delta_mul_coeff_zero hn12 s hs, add_zero] at hcoeff_sum
    exact hcoeff_sum

private lemma eval_Delta_mul_zero_imp {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12))
    (hds : (evalE₄E₆ (Delta_poly * s)) (↑n : ℤ) = 0) :
    (evalE₄E₆ s) (↑(n - 12) : ℤ) = 0 := by
  rw [map_mul, evalE₄E₆_whc_eq_single 12 Delta_poly Delta_poly_isWeightedHomogeneous,
    evalE₄E₆_whc_eq_single (n - 12) s hs, DirectSum.of_mul_of] at hds
  set D := evalE₄E₆ Delta_poly; set S := evalE₄E₆ s
  simp only [Nat.cast_ofNat] at hds
  have hcast : (12 : ℤ) + ↑(n - 12) = ↑n := by omega
  have hds2 : GradedMonoid.GMul.mul (D 12) (S (↑(n-12))) = 0 := by
    have h := hds
    rw [DirectSum.of_apply, dif_pos hcast] at h
    have : ∀ {k₁ k₂ : ℤ} (h : k₁ = k₂) (f : ModularForm Γ(1) k₁),
      h ▸ f = (0 : ModularForm Γ(1) k₂) → f = 0 := by
      intros k₁ k₂ heq f hf; cases heq; exact hf
    exact this hcast _ h
  ext z; simp only [ModularForm.zero_apply]
  have hpw := congr_fun (congr_arg (fun (f : ModularForm Γ(1) _) => f.toFun) hds2) z
  simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe,
    ModularForm.zero_apply] at hpw
  change (D 12) z * (S (↑(n-12))) z = 0 at hpw
  exact (mul_eq_zero.mp hpw).resolve_left
    (show (D 12) z ≠ 0 from evalE₄E₆_Delta_poly_grade ▸ Δ_ne_zero z)

private lemma div_Delta_poly {n : ℕ} (hn12 : 12 ≤ n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) :
    ∃ q : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight q (n - 12) ∧
      p = Delta_poly * q ∧
      (evalE₄E₆ q) (↑(n - 12) : ℤ) = 0 := by
  obtain ⟨r, s, hr_wh, hs_wh, hp_eq, hr_red⟩ := whomog_poly_Delta_decomp hn12 p hp
  have heval' : (evalE₄E₆ (r + Delta_poly * s)) (↑n : ℤ) = 0 := by rwa [← hp_eq]
  have hp_ds : p = Delta_poly * s := by
    rw [hp_eq, coeff_zero_of_eval_zero hn12 r s hr_wh hs_wh hr_red heval', zero_add]
  have hds : (evalE₄E₆ (Delta_poly * s)) (↑n : ℤ) = 0 := by rwa [← hp_ds]
  exact ⟨s, hs_wh, hp_ds, eval_Delta_mul_zero_imp hn12 s hs_wh hds⟩

private lemma per_weight_injective_inductive_step (n : ℕ)
    (ih : ∀ m < n, ∀ (p : MvPolynomial (Fin 2) ℂ),
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p m →
        (evalE₄E₆ p) (↑m : ℤ) = 0 → p = 0)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (_hk_odd : Even n) (hn12 : 12 ≤ n) : p = 0 := by
  obtain ⟨q, hq_wh, hpq, hq_eval⟩ := div_Delta_poly hn12 p hp heval
  rw [hpq, ih (n - 12) (by omega) q hq_wh hq_eval, mul_zero]

private lemma per_weight_injective_small {n : ℕ} (a b : ℕ) (ha : a < 3) (hn : n < 12)
    (hab : 4 * a + 6 * b = n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) : p = 0 := by
  obtain ⟨d₀, hd0a, hd0b⟩ := finsupp_of_fin2 a b
  apply per_weight_injective_unique_monomial p hp heval d₀
    (by rw [weight_eq_4a_6b]; omega)
  · intro d hd; have h46 := weight_eq_4a_6b d; rw [hd] at h46
    obtain ⟨hda, hdb⟩ := unique_small_weight_soln (by omega : d 0 < 3) ha
      (show d 0 * 4 + d 1 * 6 = a * 4 + b * 6 by omega)
    ext i; fin_cases i <;> [exact hda ▸ hd0a.symm; exact hdb ▸ hd0b.symm]
  · rw [hd0a, hd0b]; intro habs
    have := monomial_coeff_zero_eq_one n a b (by omega)
    rw [habs] at this; simp only [coe_zero, qExpansion_zero,
      PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_zero,
      zero_ne_one] at this

private lemma per_weight_injective_zero
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p 0)
    (heval : (evalE₄E₆ p) (0 : ℤ) = 0) : p = 0 := by
  have hpc : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
    ext d'
    simp only [MvPolynomial.coeff_C]
    by_cases hd' : 0 = d'
    · simp [hd']
    · rw [if_neg hd']
      exact hp.coeff_eq_zero d' (fun hw => hd' (by
        have h46' := weight_eq_4a_6b d'; rw [hw] at h46'
        symm; ext i; fin_cases i <;> simp [Finsupp.coe_zero] <;> omega))
  rw [hpc] at heval ⊢
  rw [evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, DirectSum.smul_apply] at heval
  have h1eq : (1 : DirectSum ℤ (fun k => ModularForm Γ(1) k)) (0 : ℤ) =
      (1 : ModularForm Γ(1) 0) := by
    conv_lhs => rw [← DirectSum.of_zero_one (fun k : ℤ => ModularForm Γ(1) k)]
    exact DirectSum.of_eq_same _ _
  rw [h1eq] at heval
  rcases smul_eq_zero.mp heval with hc | h1z
  · rw [hc, map_zero]
  · exact absurd h1z (fun h => by
      have := congr_fun (congr_arg (fun x => x.toFun) h) UpperHalfPlane.I
      simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, one_coe_eq_one,
        Pi.one_apply, zero_apply, one_ne_zero] at this)

private lemma per_weight_injective : ∀ (n : ℕ) (p : MvPolynomial (Fin 2) ℂ),
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n →
    (evalE₄E₆ p) (↑n : ℤ) = 0 → p = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp heval
  by_cases hk_odd : Odd n
  · exact whomog_eq_zero_of_no_monomials p hp (fun d => no_wt_monomial_of_odd hk_odd d)
  · rw [Nat.not_odd_iff_even] at hk_odd
    by_cases hn4 : n < 4
    · have hn02 : n = 0 ∨ n = 2 := by obtain ⟨m, rfl⟩ := hk_odd; omega
      rcases hn02 with rfl | rfl
      · exact per_weight_injective_zero p hp heval
      · exact whomog_eq_zero_of_no_monomials p hp (fun d => no_wt_monomial_of_two d)
    · push_neg at hn4
      by_cases hn12 : n < 12
      · have hn_cases : n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by
          obtain ⟨m, rfl⟩ := hk_odd; omega
        rcases hn_cases with rfl | rfl | rfl | rfl
        · exact per_weight_injective_small 1 0 (by omega) (by omega) rfl p hp heval
        · exact per_weight_injective_small 0 1 (by omega) (by omega) rfl p hp heval
        · exact per_weight_injective_small 2 0 (by omega) (by omega) rfl p hp heval
        · exact per_weight_injective_small 1 1 (by omega) (by omega) rfl p hp heval
      · push_neg at hn12
        exact per_weight_injective_inductive_step n ih p hp heval hk_odd hn12

/-- The evaluation homomorphism `evalE₄E₆` is injective
(E₄ and E₆ are algebraically independent). -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  intro p q hpq
  rw [← sub_eq_zero]
  set r := p - q with hr_def
  have hr : evalE₄E₆ r = 0 := by rw [map_sub, sub_eq_zero]; exact hpq
  rw [← MvPolynomial.sum_weightedHomogeneousComponent E₄E₆Weight r]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  exact per_weight_injective n _
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (by rw [evalE₄E₆_component_eq, hr]; rfl)

/-! ## Main isomorphism and corollaries -/

/-- The graded ring of level 1 modular forms is isomorphic to the weighted polynomial ring
in E₄ and E₆. -/
noncomputable def modularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ]
      DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

/-- E₄ and E₆ generate the entire graded ring of level 1 modular forms. -/
theorem E₄E₆_generate :
    Algebra.adjoin ℂ
      ({DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
        DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆} :
        Set (DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k))) = ⊤ := by
  rw [show ({DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
        DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆} : Set _) =
      Set.range (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _)
    from (Matrix.range_cons_cons_empty _ _ _).symm,
    Algebra.adjoin_range_eq_range_aeval,
    show MvPolynomial.aeval
        (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _) = evalE₄E₆
    from rfl]
  exact (AlgHom.range_eq_top evalE₄E₆).mpr evalE₄E₆_surjective
