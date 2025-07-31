/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib
/-!
# Continuity of series of functions

We prove some HasSumUniformlyOn versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions.

-/

open Set Metric TopologicalSpace Function Filter Complex UpperHalfPlane

open scoped Topology NNReal Nat Complex Pointwise

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn_of_bounded {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) {s} :=  by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn_of_cofinite_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) {s} := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

/- lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    (f : α → β → F) {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  apply tendstoUniformlyOn_tsum hu1 fun n x hx ↦ hu2 n ⟨x, hx⟩ -/

lemma SummableLocallyUniformlyOn_of_locally_bounded_eventually [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ᶠ n in cofinite, ∀ k ∈ K, ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n, ∀ k ∈ K, ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn_of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  refine ⟨u, hu1, by filter_upwards using hu2⟩



/-- The `derivWithin` of a absolutely and uniformly converget sum on an open set `s` is the sum
of the derivatives of squence of functions on the open set `s` -/
theorem derivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedAddCommGroup F] [NormedSpace E F] {f : α → E → F} {s : Set E}
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n , f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦(hf y hy).hasSum ) hx
    (f' := fun n : Finset α ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ Eq.symm (hg.tsum_eqOn hb)
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq ↦ ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

lemma summableUniformlyOn_differentiableOn {ι E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (h : SummableLocallyUniformlyOn (fun n ↦ ((fun z ↦ f n z))) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    DifferentiableOn ℂ (fun z ↦ ∑' n , f n z) s := by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha => (hf2 a r hr).differentiableWithinAt


lemma summable_of_tsum_ne_zero {ι α : Type*} [AddCommMonoid α] [ TopologicalSpace α]
    (g : ι → α) (h : ∑' n, g n ≠ 0) : Summable g := by
  by_contra hg
  rw [tsum_eq_zero_of_not_summable hg] at h
  aesop

variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α} {𝔖 : Set (Set β)}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α] [TopologicalSpace β] [T2Space α]

@[to_additive]
theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α]
    (s : Set β) {f f' : ι → β → α} (h : ∀ (i : ι), EqOn (f i) (f' i) s) (v : Finset ι) :
    EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s := by
  intro t ht
  simp only [Finset.prod_apply] at *
  congr
  exact funext fun i ↦ h i ht

@[to_additive]
theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α]
    (s : Set β) {f f' : ι → β → α} (h : ∀ (i : ι), EqOn (f i) (f' i) s) (v : Finset ι) :
    EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  intro t ht
  simp only at *
  congr
  exact funext fun i ↦ h i ht

@[to_additive]
lemma MultipliableLocallyUniformlyOn_congr (f f' : ι → β → α) (h : ∀ i,  s.EqOn (f i)  (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v ↦ eqOn_fun_finsetProd s h v

theorem iteratedDerivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] {f : ι → E → F} {s : Set E}
    (m : ℕ) (hs : IsOpen s) {x : E} (hx : x ∈ s) (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t))
    (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, k ≤ m → r ∈ s → DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n , f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction' m  with m hm generalizing x
  · simp
  · simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _  _ (fun n r hr ↦ hf2 n m r (by omega) hr)]
    · exact derivWithin_congr (fun t ht ↦ hm ht (fun k hk1 hkm ↦ h k hk1 (by omega))
          (fun k r e hr he ↦ hf2 k r e (by omega) he)) (hm hx (fun k hk1 hkm ↦ h k hk1 (by omega))
          (fun k r e hr he ↦ hf2 k r e (by omega) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by omega) (by omega)).summable hr).congr (fun _ ↦ by simp)
    · exact SummableLocallyUniformlyOn_congr _ _ (fun i ⦃t⦄ ht ↦ iteratedDerivWithin_succ) (h (m + 1)
      (by omega) (by omega))

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}

section

include h hx in
theorem iteratedDerivWithin_fun_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun z ↦ f z + g z) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simpa using iteratedDerivWithin_add hx h hf hg

/- theorem iteratedDerivWithin_univ_zpow (m : ℤ) (k : ℕ) :
    iteratedDerivWithin k (fun y ↦ y ^ m) univ =
    fun y ↦ (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k) := by
  simp [iteratedDerivWithin_univ, iteratedDeriv_eq_iterate] -/



theorem iteratedDerivWithin_congr_of_isOpen (f : 𝕜 → F) (n : ℕ) {s t : Set 𝕜} (hs : IsOpen s)
    (ht : IsOpen t) : (s ∩ t).EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n f t) := by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs hr.1, iteratedDerivWithin_of_isOpen ht  hr.2]



local notation "ℂ_ℤ " => Complex.integerComplement

  theorem contDiffOn_inv_linear (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z + d)) ℂ_ℤ := by
  simp only [one_div]
  apply ContDiffOn.inv
  fun_prop
  exact fun x hx ↦ Complex.integerComplement_add_ne_zero hx d

 theorem contDiffOn_inv_linear_sub (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z - d)) ℂ_ℤ := by
  simp_rw [sub_eq_add_neg]
  convert contDiffOn_inv_linear (-d) k
  simp

lemma cotTerm_iteratedDeriv (d k : ℕ) : EqOn (iteratedDeriv k (fun (z : ℂ) ↦ cotTerm z d))
    (fun z : ℂ ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ))) ℂ_ℤ := by
  intro z hz
  simp_rw [cotTerm]
  have h1 :
    (fun z : ℂ ↦ 1 / (z - (d + 1)) + 1 / (z + (d + 1))) =
      (fun z : ℂ ↦ 1 / (z - (d + 1))) + fun z : ℂ ↦ 1 / (z + (d +1)) := by rfl
  rw [h1, iteratedDeriv_add  ?_]
  · have h2 := iter_deriv_inv_linear_sub k 1 ((d + 1 : ℂ))
    have h3 := iter_deriv_inv_linear k 1 (d + 1 : ℂ)
    simp only [one_div, one_mul, one_pow, mul_one, Int.reduceNeg, iteratedDeriv_eq_iterate] at *
    rw [h2, h3]
    ring
  · simpa using (contDiffOn_inv_linear (d + 1) k).contDiffAt
      (IsOpen.mem_nhds ( (by apply Complex.isOpen_compl_range_intCast)) hz)
  · simpa using (contDiffOn_inv_linear_sub (d + 1) k).contDiffAt
      (IsOpen.mem_nhds ( (by apply Complex.isOpen_compl_range_intCast)) hz)

lemma cotTerm_iteratedDerivWith (d k : ℕ) : EqOn (iteratedDerivWithin k (fun (z : ℂ) ↦ cotTerm z d) ℂ_ℤ)
    (fun z : ℂ ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ))) ℂ_ℤ := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast)
  apply cotTerm_iteratedDeriv

lemma upperHalfPlane_inter_integerComplement :
    {z : ℂ | 0 < z.im} ∩ Complex.integerComplement = {z : ℂ | 0 < z.im} := by
  ext z
  simp
  intro hz
  apply UpperHalfPlane.coe_mem_integerComplement ⟨z,hz⟩

lemma UpperHalPlane_isOpen : IsOpen {z : ℂ | 0 < z.im} := by
  exact (isOpen_lt continuous_const Complex.continuous_im)

lemma cotTerm_iteratedDerivWith' (d k : ℕ) : EqOn
    (iteratedDerivWithin k (fun (z : ℂ) ↦ cotTerm z d) {z : ℂ | 0 < z.im})
    (fun z : ℂ ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
    {z : ℂ | 0 < z.im} := by
  have h1 : IsOpen ℂ_ℤ := by apply Complex.isOpen_compl_range_intCast
  have := iteratedDerivWithin_congr_of_isOpen (fun (z : ℂ) ↦ cotTerm z d) k UpperHalPlane_isOpen h1
  rw [upperHalfPlane_inter_integerComplement] at this
  apply Set.EqOn.trans this
  intro z hz
  simpa using cotTerm_iteratedDerivWith d k (UpperHalfPlane.coe_mem_integerComplement ⟨z,hz⟩)

lemma abs_norm_eq_max_natAbs (n : ℕ) :
    ‖![1, (n + 1 : ℤ)]‖ = n + 1 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, EisensteinSeries.norm_eq_max_natAbs, Fin.isValue,
    Matrix.cons_val_zero, isUnit_one, Int.natAbs_of_isUnit, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Nat.cast_max, Nat.cast_one]
  norm_cast
  simp

lemma abs_norm_eq_max_natAbs_neg (n : ℕ) :
    ‖![1, -(n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero, isUnit_one,
    Int.natAbs_of_isUnit, Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, Int.natAbs_neg]
  norm_cast
  simp

open EisensteinSeries

private noncomputable abbrev cotTermUpperBound (A B : ℝ) (hB : 0 < B) (k a : ℕ) :=
  k ! * (2 * (r (⟨⟨A, B⟩, by simp [hB]⟩) ^ (-1 - (k : ℤ))) * ‖ ((a + 1) ^ (-1 - (k : ℤ)) : ℝ)‖)

private lemma Summable_cotTermUpperBound (A B : ℝ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k) :
    Summable fun a : ℕ ↦ cotTermUpperBound A B hB k a := by
  simp_rw [← mul_assoc]
  apply Summable.mul_left
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
      (EisensteinSeries.linear_right_summable 0 1 (k := k + 1) (by omega))).1).norm.congr
  simp only [Int.cast_one, mul_zero, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast,
    zero_add, ← zpow_neg, neg_add_rev, Int.reduceNeg, norm_zpow, sub_eq_add_neg, Real.norm_eq_abs]
  norm_cast
  exact fun n ↦ rfl

private lemma iteratedDeriv_CotTerm_bounded_uniformly {k : ℕ} (hk : 1 ≤ k) (K : Set ℂ)
  (hK : K ⊆ {z | 0 < z.im}) (A B : ℝ) (hB : 0 < B)
  (HABK : inclusion hK '' univ ⊆ verticalStrip A B) (n : ℕ) (a : ℂ) (ha : a ∈ K):
    ‖iteratedDerivWithin k (fun z ↦ cotTerm z n) {z | 0 < z.im} a‖ ≤ cotTermUpperBound A B hB k n := by
  simp only [cotTerm_iteratedDerivWith' n k (hK ha), Complex.norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, norm_natCast, one_mul, cotTermUpperBound, Int.reduceNeg, norm_zpow,
    Real.norm_eq_abs, two_mul, add_mul]
  gcongr
  apply le_trans (norm_add_le _ _)
  apply add_le_add
  · have := summand_bound_of_mem_verticalStrip (k := (k + 1)) (by norm_cast; omega) ![1, n+1] hB
      (z := ⟨a, (hK ha)⟩) (A := A) (by aesop)
    simp only [coe_setOf, image_univ, Fin.isValue, Matrix.cons_val_zero, Int.cast_one,
      coe_mk_subtype, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_add,
      Int.cast_natCast, neg_add_rev, abs_norm_eq_max_natAbs, Int.reduceNeg, sub_eq_add_neg,
      norm_zpow, ge_iff_le] at *
    norm_cast at *
  · have := summand_bound_of_mem_verticalStrip (k := k + 1) (by norm_cast; omega) ![1, -(n + 1)] hB
      (z := ⟨a, (hK ha)⟩) (A := A) (by aesop)
    rw [abs_norm_eq_max_natAbs_neg] at this
    simp only [coe_setOf, image_univ, neg_add_rev, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero,
      Int.cast_one, coe_mk_subtype, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_add, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg, norm_zpow, ge_iff_le] at *
    norm_cast at *

lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm (k : ℕ) (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn
    (fun n : ℕ ↦ iteratedDerivWithin k (fun z : ℂ ↦ cotTerm z n) {z : ℂ | 0 < z.im})
      {z : ℂ | 0 < z.im} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded (UpperHalPlane_isOpen)
  intro K hK hKc
  have hKK2 : IsCompact (Set.image (inclusion hK) univ) := by
    apply IsCompact.image_of_continuousOn
    · exact isCompact_iff_isCompact_univ.mp hKc
    · exact continuous_inclusion hK |>.continuousOn
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hKK2
  exact ⟨cotTermUpperBound A B hB k, Summable_cotTermUpperBound A B hB hk,
    iteratedDeriv_CotTerm_bounded_uniformly hk K hK A B hB HABK⟩

theorem iteratedDeriv_cotTerm_DifferentiableOn (n l : ℕ) :
    DifferentiableOn ℂ (iteratedDerivWithin l (fun z ↦ cotTerm z n) {z | 0 < z.im})
    {z : ℂ | 0 < z.im} := by
  suffices DifferentiableOn ℂ
    (fun z : ℂ ↦ (-1) ^ l * l ! * ((z + (n + 1)) ^ (-1 - l : ℤ) + (z - (n + 1)) ^ (-1 - l : ℤ)))
      {z : ℂ | 0 < z.im} by
    apply this.congr
    intro z hz
    simpa using (cotTerm_iteratedDerivWith' n l hz)
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.add <;> apply DifferentiableOn.zpow
  any_goals try {fun_prop} <;> left <;> intro x hx
  · simpa [add_eq_zero_iff_neg_eq'] using (UpperHalfPlane.ne_int ⟨x, hx⟩ (-(n+1))).symm
  · simpa [sub_eq_zero] using (UpperHalfPlane.ne_int ⟨x, hx⟩ ((n+1)))

private theorem aux_summable_add (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
  Summable fun (n : ℕ) ↦ ((x : ℂ) + (n + 1)) ^ (-1 - k : ℤ) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by omega))).1).congr
  simp [← zpow_neg, sub_eq_add_neg]

private theorem aux_summable_neg (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
  Summable fun (n : ℕ) ↦ ((x : ℂ) - (n + 1)) ^ (-1 - k : ℤ) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by omega))).2).congr
  simp [← zpow_neg, sub_eq_add_neg]

private theorem aux_iteratedDeriv_tsum_cotTerm (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
    (-1) ^ k * (k !) * (x : ℂ) ^ (-1 - k : ℤ) + iteratedDerivWithin k
        (fun z : ℂ ↦ ∑' n : ℕ, cotTerm z n) {z : ℂ | 0 < z.im}  x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, ((x : ℂ) + n) ^ (-1  - k : ℤ) := by
    rw [iteratedDerivWithin_tsum k UpperHalPlane_isOpen
       (by simpa using x.2) (fun t ht ↦ Summable_cotTerm (coe_mem_integerComplement ⟨t, ht⟩))
       (fun l hl hl2 ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm l hl)
       (fun n l z hl hz ↦ ((iteratedDeriv_cotTerm_DifferentiableOn n l)).differentiableAt
       ((IsOpen.mem_nhds (UpperHalPlane_isOpen) hz)))]
    conv =>
      enter [1,2,1]
      ext n
      rw [cotTerm_iteratedDerivWith' n k (by simp [UpperHalfPlane.coe])]
    rw [tsum_of_add_one_of_neg_add_one (by simpa using aux_summable_add k hk x)
      (by simpa [sub_eq_add_neg] using aux_summable_neg k hk x),
      tsum_mul_left, Summable.tsum_add (aux_summable_add k hk x) (aux_summable_neg k hk x )]
    simp only [Int.reduceNeg, sub_eq_add_neg, neg_add_rev, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Int.cast_zero, add_zero, Int.cast_neg]
    ring

open Real
theorem cot_series_rep_deriv (k : ℕ) (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun x ↦ π * Complex.cot (π * x) - 1 / x) {z : ℂ | 0 < z.im} z =
    -(-1) ^ k * (k !) * ((z : ℂ) ^ (-1 - k : ℤ)) +
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, ((z : ℂ) + n) ^ (-1 - k : ℤ):= by
  rw [← aux_iteratedDeriv_tsum_cotTerm k hk]
  simp only [one_div, neg_mul, neg_add_cancel_left]
  refine iteratedDerivWithin_congr ?_ z.2
  intro x hx
  simpa [cotTerm] using (cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement ⟨x, hx⟩))

theorem cot_pi_z_contDiffWithinAt (k : ℕ) (z : ℍ) :
  ContDiffWithinAt ℂ (k) (fun x ↦ (↑π * x).cot) {z | 0 < z.im} (z : ℂ) := by
  simp_rw [Complex.cot, Complex.cos]
  apply ContDiffWithinAt.div
  fun_prop
  simp_rw [Complex.sin]
  fun_prop
  apply sin_pi_z_ne_zero (UpperHalfPlane.coe_mem_integerComplement z)

theorem cot_series_rep_deriv2 (k : ℕ) (z : ℍ) :
    iteratedDerivWithin k (fun x ↦ π * Complex.cot (π * x) - 1 / x) {z : ℂ | 0 < z.im} z =
      (iteratedDerivWithin k (fun x ↦ π * Complex.cot (π * x)) {z : ℂ | 0 < z.im} z)
        -(-1) ^ k * (k !) * ((z : ℂ) ^ (-1 - k : ℤ)) := by
  simp_rw [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add]
  · simpa  [iteratedDerivWithin_fun_neg] using iteratedDerivWithin_one_div k UpperHalPlane_isOpen z.2
  · apply z.2
  · refine IsOpen.uniqueDiffOn UpperHalPlane_isOpen
  · refine ContDiffWithinAt.smul ?_ ?_
    fun_prop
    apply cot_pi_z_contDiffWithinAt k z
  · simp
    apply ContDiffWithinAt.neg
    apply ContDiffWithinAt.inv
    fun_prop
    exact ne_zero z

theorem cot_series_rep_iteratedDeriv (k : ℕ) (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun x ↦ π * Complex.cot (π * x)) {z : ℂ | 0 < z.im} z =
      (-1) ^ k * (k : ℕ)! * ∑' n : ℤ, ((z : ℂ) + n) ^ (-1 - k : ℤ):= by
  have h0 := cot_series_rep_deriv2 k z
  rw [cot_series_rep_deriv k hk z, add_comm] at h0
  rw [← add_left_inj (-(-1) ^ k * ↑k ! * (z : ℂ) ^ (-1 - k : ℤ)), h0]
  ring

theorem cot_series_rep_iteratedDeriv_one_div (k : ℕ) (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun x ↦ π * Complex.cot (π * x)) {z : ℂ | 0 < z.im} z =
      (-1) ^ k * (k : ℕ)! * ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1):= by
  simp only [cot_series_rep_iteratedDeriv k hk z, Int.reduceNeg, one_div, mul_eq_mul_left_iff,
    mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq,  Nat.cast_eq_zero,
    show -1 - (k : ℤ) = -(k + 1) by ring]
  left ; rfl

abbrev cup := {z : ℂ | 0 < z.im}

local notation "ℍₒ" => cup

lemma exp_iter_deriv_within (k m : ℕ) (f : ℕ → ℂ) (p : ℝ) :
    EqOn (iteratedDerivWithin k (fun s : ℂ => (f m) * Complex.exp (2 * ↑π * Complex.I * m * s / p)) ℍₒ)
      (fun s => (f m) * (2 * ↑π * Complex.I * m / p) ^ k * Complex.exp (2 * ↑π * Complex.I * m * s / p)) ℍₒ := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen UpperHalPlane_isOpen)
  intro x hx
  rw [iteratedDeriv_const_mul]
  · have : (fun s ↦ cexp (2 * ↑π * Complex.I * ↑m * s / ↑p)) =
      (fun s ↦ cexp (((2 * ↑π * Complex.I * ↑m) / p) * s)) := by
      ext z
      ring_nf
    simp only [this, iteratedDeriv_cexp_const_mul]
    ring_nf
  · fun_prop

lemma exp_iter_deriv_within2 (k m : ℕ) (p : ℝ) :
    EqOn (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * m * s / p)) ℍₒ)
      (fun s => (2 * ↑π * Complex.I * m / p) ^ k * Complex.exp (2 * ↑π * Complex.I * m * s / p)) ℍₒ := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen UpperHalPlane_isOpen)
  intro x hx
  have : (fun s ↦ cexp (2 * ↑π * Complex.I * ↑m * s / ↑p)) =
    (fun s ↦ cexp (((2 * ↑π * Complex.I * ↑m) / p) * s)) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf


/- open Nat Asymptotics in
theorem summable_norm_mul_geometric_of_norm_lt_one_complex {k : ℕ} {r : ℝ}
    (hr : ‖r‖ < 1) {u : ℕ → ℂ} (hu : u =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  rw [← norm_norm] at hrr'
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
  calc
  fun n ↦ ‖(u n) * r ^ n‖
  _ =O[atTop] fun n ↦ ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : ℝ)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n ↦ ↑(n ^ k) * ‖r‖ ^ n := (Asymptotics.isBigO_norm_left.mpr hu).mul (isBigO_refl _ _)
  _ =O[atTop] fun n ↦ r' ^ n := by
      simp only [cast_pow]
      exact (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO
 -/
open Nat Asymptotics in
theorem summable_norm_mul_geometric_of_norm_lt_one' {F : Type*} [NormedRing F]
    [NormOneClass F] [NormMulClass F] {k : ℕ} {r : F} (hr : ‖r‖ < 1) {u : ℕ → F}
    (hu : u =O[atTop] (fun n ↦ ((n ^ k : ℕ) : F))) : Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h).norm
  calc
  fun n ↦ ‖(u n) * r ^ n‖
  _ =O[atTop] fun n ↦ ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : ℝ)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n ↦ ‖((n : F) ^ k)‖ * ‖r‖ ^ n := by
      simpa [Nat.cast_pow] using (Asymptotics.isBigO_norm_left.mpr
      (Asymptotics.isBigO_norm_right.mpr hu)).mul (isBigO_refl (fun n => (‖r‖ ^ n)) atTop)
  _ =O[atTop] fun n ↦ ‖r' ^ n‖ := by
      convert Asymptotics.isBigO_norm_right.mpr (Asymptotics.isBigO_norm_left.mpr
        (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO)
      simp only [norm_pow, norm_mul]

lemma aux_IsBigO_mul (k : ℕ) (p : ℝ) {f : ℕ → ℂ} (hf : f =O[atTop] (fun n => (↑(n ^ k) : ℝ))) :
    (fun n => f n * (2 * ↑π * Complex.I * ↑n / p) ^ k) =O[atTop]
    (fun n => (↑(n ^ (2 * k)) : ℝ)) := by
  have h0 : (fun n : ℕ => (2 * ↑π * Complex.I * ↑n / p) ^ k) =O[atTop]
    (fun n => (↑(n ^ (k)) : ℝ)) := by
    have h1 : (fun n : ℕ => (2 * ↑π * Complex.I * ↑n / p) ^ k) =
      (fun n : ℕ => ((2 * ↑π * Complex.I / p) ^ k) * ↑n ^ k) := by
      ext z
      ring
    simpa [h1] using (Complex.isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * ↑π * Complex.I / p) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop))
  simp only [Nat.cast_pow] at *
  convert hf.mul h0
  ring

lemma aux_IsBigO_mul2 (k l : ℕ) (p : ℝ) {f : ℕ → ℂ} (hf : f =O[atTop] (fun n => (↑(n ^ l) : ℝ))) :
    (fun n => f n * (2 * ↑π * Complex.I * ↑n / p) ^ k) =O[atTop]
    (fun n => (↑(n ^ (l + k)) : ℝ)) := by
  have h0 : (fun n : ℕ => (2 * ↑π * Complex.I * ↑n / p) ^ k) =O[atTop]
    (fun n => (↑(n ^ (k)) : ℝ)) := by
    have h1 : (fun n : ℕ => (2 * ↑π * Complex.I * ↑n / p) ^ k) =
      (fun n : ℕ => ((2 * ↑π * Complex.I / p) ^ k) * ↑n ^ k) := by
      ext z
      ring
    simpa [h1] using (Complex.isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * ↑π * Complex.I / p) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop))
  simp only [Nat.cast_pow] at *
  convert hf.mul h0
  ring

lemma exp_nsmul' (x a p : ℂ) (n : ℕ) : exp (a * n * x / p) = exp (a * x / p) ^ n := by
  rw [← Complex.exp_nsmul]
  ring_nf

open BoundedContinuousFunction in
theorem qExpansion_summableLocallyUniformlyOn (k : ℕ) {f : ℕ → ℂ} {p : ℝ} (hp : 0 < p)
    (hf : f =O[atTop] (fun n => (↑(n ^ k) : ℝ))) : SummableLocallyUniformlyOn
    (fun n ↦ iteratedDerivWithin k (fun z ↦ f n * cexp (2 * ↑π * Complex.I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded UpperHalPlane_isOpen
  intro K hK hKc
  haveI : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K => Complex.exp (2 * ↑π * Complex.I * r / p), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * ↑π * Complex.I * (↑x / ↑p)) = cexp (2 * ↑π * Complex.I * ↑x / ↑p) := by
      congr 1
      ring
    simpa using h1 ▸ UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / p) , by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k p hf))), ?_⟩
  intro n z hz
  have h0 := pow_le_pow_left₀ (by apply norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [← exp_nsmul', exp_iter_deriv_within k n f p (hK hz), Complex.norm_mul, norm_pow,
    Complex.norm_div, Complex.norm_ofNat, norm_real, norm_eq_abs, norm_I, mul_one,
    Complex.norm_natCast,Nat.cast_pow, norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk,
    abs_norm, ge_iff_le, r, c] at *
  gcongr
  convert h0
  rw [← norm_pow, ← exp_nsmul']

open BoundedContinuousFunction in
theorem qExpansion_summableLocallyUniformlyOn2 (k l : ℕ) {f : ℕ → ℂ} {p : ℝ} (hp : 0 < p)
    (hf : f =O[atTop] (fun n => (↑(n ^ l) : ℝ))) : SummableLocallyUniformlyOn
    (fun n ↦ (f n) • iteratedDerivWithin k (fun z ↦  cexp (2 * ↑π * Complex.I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded UpperHalPlane_isOpen
  intro K hK hKc
  haveI : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K => Complex.exp (2 * ↑π * Complex.I * r / p), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * ↑π * Complex.I * (↑x / ↑p)) = cexp (2 * ↑π * Complex.I * ↑x / ↑p) := by
      congr 1
      ring
    simpa using h1 ▸ UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / p) , by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul2 k l p hf))), ?_⟩
  intro n z hz
  have h0 := pow_le_pow_left₀ (by apply norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp
  simp only [Nat.cast_pow, norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ←
    exp_nsmul', exp_iter_deriv_within2 k n p (hK hz), norm_mul, norm_pow, norm_div,
    RCLike.norm_ofNat, norm_real, norm_eq_abs, norm_I, mul_one, RCLike.norm_natCast, abs_norm, r,
    c] at *
  rw [← mul_assoc]
  gcongr
  convert h0
  rw [← norm_pow, ← exp_nsmul']

theorem cot_q_ext_summableLocallyUniformlyOn (k : ℕ) : SummableLocallyUniformlyOn
    (fun n ↦ iteratedDerivWithin k (fun z ↦ cexp (2 * ↑π * Complex.I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : ℕ => (1 : ℂ)) =O[atTop] (fun n => (↑(n ^ k) : ℝ)) := by
    simp only [Nat.cast_pow, Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast,
      eventually_atTop, ge_iff_le]
    refine ⟨1, 1, fun b hb => ?_⟩
    norm_cast
    simp [Nat.one_le_pow k b hb]
  simpa using qExpansion_summableLocallyUniformlyOn k (p := 1) (by norm_num) h0

theorem deriv_iterderivwithin (n a : ℕ) {s : Set ℂ} (hs : IsOpen s) {r : ℂ} (hr : r ∈ s) :
    DifferentiableAt ℂ (iteratedDerivWithin a (fun z ↦ cexp (2 * ↑π * Complex.I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt
  suffices DifferentiableOn ℂ (iteratedDeriv a (fun z ↦ cexp (2 * ↑π * Complex.I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop
  exact hs.mem_nhds hr

lemma exp_deriv' (k : ℕ) (z : ℍ) : iteratedDerivWithin k
    (fun z => ( ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n)) {z : ℂ | 0 < z.im} z =
    ∑' n : ℕ, iteratedDerivWithin k
    (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * s) ^ n) {z : ℂ | 0 < z.im} z := by
  rw [iteratedDerivWithin_tsum k UpperHalPlane_isOpen (by simpa using z.2)]
  · exact fun x hx => summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ => cot_q_ext_summableLocallyUniformlyOn n
  · exact fun n l z hl hz => deriv_iterderivwithin n l UpperHalPlane_isOpen hz

theorem tsum_uexp_contDiffOn (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, Complex.exp (2 * ↑π * Complex.I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz =>
  ((summableUniformlyOn_differentiableOn UpperHalPlane_isOpen
  (cot_q_ext_summableLocallyUniformlyOn m)
  (fun n _ hz => deriv_iterderivwithin n m UpperHalPlane_isOpen hz)) z hz).congr
  (fun z hz => exp_deriv' m ⟨z, hz⟩) (exp_deriv' m ⟨z, hz⟩)

lemma exp_deriv {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
  iteratedDerivWithin k
    (fun z => (((π : ℂ) * Complex.I) -
    (2 * π * Complex.I) * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n)) {z : ℂ | 0 < z.im} z =
    -(2 * π * Complex.I) * ∑' n : ℕ, iteratedDerivWithin k
    (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * s) ^ n) {z : ℂ | 0 < z.im} z := by
  rw [iteratedDerivWithin_const_sub hk , iteratedDerivWithin_fun_neg, iteratedDerivWithin_const_mul]
  · simp only [exp_deriv', neg_mul]
  · simpa using z.2
  · exact UpperHalPlane_isOpen.uniqueDiffOn
  · exact (tsum_uexp_contDiffOn k).contDiffWithinAt (by simpa using z.2)

lemma exp_deriv4 {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
  iteratedDerivWithin k
    (fun z => (((π : ℂ) * Complex.I) -
    (2 * π * Complex.I) * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n)) ℍₒ z =
    -(2 * π * Complex.I) ^ (k + 1) * ∑' n : ℕ, n ^ k * Complex.exp (2 * ↑π * Complex.I * z) ^ n := by
  have : -(2 * ↑π * Complex.I * (2 * ↑π * Complex.I) ^ k) *
    ∑' (n : ℕ), ↑n ^ k * cexp (2 * ↑π * Complex.I * ↑z) ^ n = -(2 * π * Complex.I) *
    ∑' n : ℕ, (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * z) ^ n := by
    simp_rw [← tsum_mul_left]
    congr
    ext y
    ring
  simp only [exp_deriv hk z, neg_mul, show k + 1 = 1 + k by ring, pow_add, pow_one, this, neg_inj,
    mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, I_ne_zero,
    or_false, Real.pi_ne_zero]
  congr
  ext n
  have := exp_nsmul' (p := 1) (a := 2 * π * Complex.I) (n := n)
  simp only [div_one] at this
  simpa [this, ofReal_one, div_one, one_mul, UpperHalfPlane.coe] using
    exp_iter_deriv_within k n (fun n => 1) 1 z.2

theorem Eisenstein_qExpansion_identity {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    (-1) ^ k * (k : ℕ)! * ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    -(2 * π * Complex.I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ n := by
  rw [← exp_deriv4 hk z, ← cot_series_rep_iteratedDeriv_one_div k hk z]
  apply iteratedDerivWithin_congr
  · intro x hx
    simpa using pi_mul_cot_pi_q_exp  ⟨x, hx⟩
  · simpa using z.2

theorem Eisenstein_qExpansion_identity' {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    ((-2 * π * Complex.I) ^ (k + 1) / (k !)) *
    ∑' n : ℕ, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ n := by
  simp_rw [(eq_inv_mul_iff_mul_eq₀ (by simp [Nat.factorial_ne_zero])).mpr
    (Eisenstein_qExpansion_identity hk z), ← tsum_mul_left]
  congr
  ext n
  have h3 : (k ! : ℂ) ≠ 0 := by
      norm_cast
      apply Nat.factorial_ne_zero
  rw [show (-2 * ↑π * Complex.I) ^ (k + 1) = (-1)^ (k + 1) * (2 * π * Complex.I) ^ (k + 1) by
       rw [← neg_pow]; ring]
  field_simp [h3]
  ring_nf
  simp [Nat.mul_two]

lemma tsum_pnat_eq_tsum_succ4 {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α]
  (f : ℕ → α) (hf : Summable f) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n := by
  rw [Summable.tsum_eq_zero_add hf]
  simp
  exact tsum_pnat_eq_tsum_succ f




open  ArithmeticFunction

def mapdiv (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ := by
  refine fun x =>
   ⟨⟨x.1.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal x.2)⟩,
    (⟨x.1.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩ : ℕ+),
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩

def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+ where
  toFun x := mapdiv x.1 x.2
  invFun x :=
    ⟨⟨x.1.1 * x.2.1, mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by
      simp only [PNat.mk_coe, Nat.mem_divisorsAntidiagonal, ne_eq, mul_eq_zero, not_or]
      refine ⟨rfl, PNat.ne_zero x.1, PNat.ne_zero x.2⟩⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    simp_rw [mapdiv, PNat.mk_coe]
    ext <;> simp [h] at *
    rfl
  right_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    simp_rw [mapdiv]
    norm_cast
    rfl

theorem sigma_eq_sum_div' (k n : ℕ) : sigma k n = ∑ d ∈ Nat.divisors n, (n / d) ^ k := by
  rw [sigma, ArithmeticFunction.coe_mk, ← Nat.sum_div_divisors]



/- theorem a3334 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c) := by
  have he : 0 < (e * (z : ℂ)).im := by
    simpa using z.2
  apply ((qExpansion_summableLocallyUniformlyOn2 0 k (p := 1) (f := fun n => (n ^ k : ℂ))
    (by norm_num) (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  intro b
  simp only [ofReal_one, div_one, ← Complex.exp_nsmul, nsmul_eq_mul, iteratedDerivWithin_zero,
    Pi.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq]
  left
  ring_nf

theorem a333 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ+ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c) := by
  apply (a3334 k e z).subtype

theorem Eisenstein_qExpansion_identity'' {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    ((-2 * π * Complex.I) ^ (k + 1) / (k !)) *
    ∑' n : ℕ+, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ (n : ℕ) := by
  have hk0 : k ≠ 0 := by omega
  rw [Eisenstein_qExpansion_identity' hk z, ← tsum_pnat_eq_tsum_succ4]
  simp only [neg_mul, CharP.cast_eq_zero, ne_eq, hk0, not_false_eq_true, zero_pow, pow_zero,
    mul_one, zero_add]
  apply (a3334 k 1 z).congr
  simp only [PNat.val_ofNat, Nat.cast_one, mul_one, ← Complex.exp_nsmul, nsmul_eq_mul,
    mul_eq_mul_left_iff, ne_eq, hk0, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
  intro b
  left
  ring_nf

theorem summable_auxil_13 (k : ℕ) (z : ℍ) :
    Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦
    (c.2.1).1 ^ k * cexp (2 * ↑π * Complex.I * ↑z * c.2.1.1 * c.2.1.2) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg]
  constructor
  · apply fun n => (hasSum_fintype _).summable
  · simp only [Complex.norm_mul, norm_pow, Complex.norm_natCast, tsum_fintype,
    Finset.univ_eq_attach]
    · apply Summable.of_nonneg_of_le (fun b => Finset.sum_nonneg (by simp)) ?_
        (summable_norm_iff.mpr (a333 (k+1) 1 z))
      intro b
      apply le_trans (b := ∑ _ ∈ (b : ℕ).divisors, b ^ k * ‖exp (2 * ↑π * Complex.I * ↑z * b)‖)
      · simp only [Finset.sum_attach ((b : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
            (x.1 : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x.1 * x.2)‖),
        Nat.sum_divisorsAntidiagonal ((fun (x : ℕ) => fun (y : ℕ) =>
            (x : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * z * x * y)‖))]
        gcongr <;> rename_i i hi <;> simp at hi
        · exact Nat.le_of_dvd b.2 hi
        · apply le_of_eq
          rw [mul_assoc]
          congr
          norm_cast
          exact Nat.mul_div_cancel' hi
      · simpa [← mul_assoc, add_comm k 1, pow_add] using Nat.card_divisors_le_self b
  · simp

theorem tsum_sigma_eqn2 (k : ℕ) (z : ℍ) :
    ∑' (c : Fin 2 → ℕ+), (c 0 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * z * c 0 * c 1) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * z * e) := by
  rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq, ← sigmaAntidiagonalEquivProd.tsum_eq]
  simp [sigmaAntidiagonalEquivProd, mapdiv, sigma_eq_sum_div']
  rw [ Summable.tsum_sigma ]
  apply tsum_congr
  · intro n
    simp only [tsum_fintype, Finset.univ_eq_attach,
      Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
      (fun (x : ℕ × ℕ) => (x.1 : ℂ) ^ k * cexp (2 * ↑π * Complex.I * z * x.1 * x.2)),
      Nat.sum_divisorsAntidiagonal' (fun x y => (x : ℂ) ^ k * cexp (2 * ↑π * Complex.I * z * x * y))
      (n := n), Finset.sum_mul]
    apply Finset.sum_congr (rfl)
    intro i hi
    have hni : (n / i : ℕ) * (i : ℂ) = n := by
      norm_cast
      simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at *
      exact Nat.div_mul_cancel hi
    simp [mul_assoc, hni]
  · exact summable_auxil_13 k z -/

theorem a3334 (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z) ^ c := by
  have he : 0 < (e * (z : ℂ)).im := by
    simpa using z.2
  apply ((qExpansion_summableLocallyUniformlyOn2 0 k (p := 1) (f := fun n => (n ^ k : ℂ))
    (by norm_num) (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  intro b
  simp only [ofReal_one, div_one, ← Complex.exp_nsmul, nsmul_eq_mul, iteratedDerivWithin_zero,
    Pi.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq]
  left
  ring_nf

theorem Eisenstein_qExpansion_identity'' {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    ((-2 * π * Complex.I) ^ (k + 1) / (k !)) *
    ∑' n : ℕ+, n ^ k * cexp (2 * ↑π * Complex.I * z) ^ (n : ℕ) := by
  have hk0 : k ≠ 0 := by omega
  rw [Eisenstein_qExpansion_identity' hk z, ← tsum_pnat_eq_tsum_succ4]
  simp only [neg_mul, CharP.cast_eq_zero, ne_eq, hk0, not_false_eq_true, zero_pow, pow_zero,
    mul_one, zero_add]
  apply (a3334 k 1 z).congr
  simp

theorem summable_auxil_13 (k : ℕ) (z : ℍ) :
    Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦
    (c.2.1).1 ^ k * cexp (2 * ↑π * Complex.I * c.2.1.2 * z) ^ c.2.1.1 := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg]
  constructor
  · apply fun n => (hasSum_fintype _).summable
  · simp only [Complex.norm_mul, norm_pow, Complex.norm_natCast, tsum_fintype,
    Finset.univ_eq_attach]
    · apply Summable.of_nonneg_of_le (fun b => Finset.sum_nonneg (by simp)) ?_ ((summable_norm_iff
      (f := fun c : ℕ+ => (c : ℂ) ^ (k + 1) * exp (2 * ↑π * Complex.I * (1: ℕ+) * ↑z) ^ (c : ℕ)).mpr
      (by apply (a3334 (k+1) 1 z).subtype)))
      intro b
      apply le_trans (b := ∑ _ ∈ (b : ℕ).divisors, b ^ k * ‖exp (2 * ↑π * Complex.I * ↑z) ^ (b : ℕ)‖)
      · rw [Finset.sum_attach ((b : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
            (x.1 : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * x.2 * z)‖ ^ x.1),
          Nat.sum_divisorsAntidiagonal ((fun x y =>
          (x : ℝ) ^ (k : ℕ) * ‖Complex.exp (2 * ↑π * Complex.I * y * z)‖ ^ x))]
        gcongr <;> rename_i i hi <;> simp at hi
        · exact Nat.le_of_dvd b.2 hi
        · apply le_of_eq
          simp_rw [mul_assoc, ← norm_pow, ← Complex.exp_nsmul]
          nth_rw 2 [← Nat.mul_div_cancel' hi]
          simp
          ring_nf
      · simpa [← mul_assoc, add_comm k 1, pow_add] using Nat.card_divisors_le_self b
  · simp

theorem tsum_sigma_eqn2 (k : ℕ) (z : ℍ) :
    ∑' (c : ℕ+ × ℕ+), (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * c.2 * z) ^ (c.1 : ℕ) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * z) ^ (e : ℕ) := by
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  simp [sigmaAntidiagonalEquivProd, mapdiv, sigma_eq_sum_div']
  rw [Summable.tsum_sigma ]
  apply tsum_congr
  · intro n
    simp only [tsum_fintype, Finset.univ_eq_attach,
      Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
      (fun (x : ℕ × ℕ) => (x.1 : ℂ) ^ k * cexp (2 * ↑π * Complex.I * x.2 * z) ^ x.1),
      Nat.sum_divisorsAntidiagonal' (fun x y => (x : ℂ) ^ k * cexp (2 * ↑π * Complex.I * y * z) ^ x),
      Finset.sum_mul]
    refine Finset.sum_congr (rfl) fun i hi => ?_
    have hni : (n / i : ℕ) * (i : ℂ) = n := by
      norm_cast
      simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at *
      exact Nat.div_mul_cancel hi
    simp only [← Complex.exp_nsmul, nsmul_eq_mul, ← hni, mul_eq_mul_left_iff, pow_eq_zero_iff',
      Nat.cast_eq_zero, Nat.div_eq_zero_iff, ne_eq]
    left
    ring_nf
  · exact summable_auxil_13 k z


theorem as1 (k : ℕ) (z : ℍ) :
    Summable fun c : ℕ+ × ℕ+ ↦ (c.1 ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * c.2 * z) ^ (c.1 : ℕ) := by
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp [sigmaAntidiagonalEquivProd, mapdiv]
  apply summable_auxil_13 k z


theorem tsum_sigma_eqn22 (k : ℕ) (z : ℍ) :
    ∑' d : ℕ+, ∑' (c : ℕ+), (c ^ k : ℂ) * Complex.exp (2 * ↑π * Complex.I * d * z) ^ (c : ℕ) =
      ∑' e : ℕ+, sigma k e * Complex.exp (2 * ↑π * Complex.I * z) ^ (e : ℕ) := by
  have := tsum_sigma_eqn2 k z
  rw [Summable.tsum_prod  (as1 k z), Summable.tsum_comm ] at this
  · simpa using this
  · apply (as1 k z).prod_symm.congr
    simp


theorem int_nat_sum {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  [CompleteSpace α]
  (f : ℤ → α) : Summable f → Summable fun x : ℕ => f x := by
  intro h
  rw [summable_int_iff_summable_nat_and_neg] at h
  apply h.1

theorem HasSum.nonneg_add_neg {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) := by
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl

theorem HasSum.pos_add_zero_add_neg {α : Type*} [TopologicalSpace α] [AddCommGroup α]
    [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) := by
    intro g hg
    simpa using (hasSum_nat_add_iff _).mp hg
  (this (fun n => f n) hpos).nonneg_add_neg hneg

theorem pnat_multipliable_iff_multipliable_succ2 {R α : Type*} [Semiring R] [TopologicalSpace α] [CommMonoid α]
    {f : R → α} : Multipliable (fun x : ℕ+ => f x) ↔ Multipliable fun x : ℕ => f (x + 1) := by
  convert Equiv.pnatEquivNat.symm.multipliable_iff.symm
  simp

theorem pnat_summable_iff_summable_succ2 {α R : Type*} [Semiring R] [TopologicalSpace α] [AddCommMonoid α]
    {f : R → α} : Summable (fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1) := by
  convert Equiv.pnatEquivNat.symm.summable_iff.symm
  simp

theorem tprod_pnat_eq_tprod_succ2 {R α : Type*} [Semiring R] [TopologicalSpace α] [CommMonoid α]
    (f : R → α) : ∏' n : ℕ+, f n = ∏' (n : ℕ), f (n + 1) := by
  convert  (Equiv.pnatEquivNat.symm.tprod_eq _).symm
  simp

theorem tsum_pnat_eq_tsum_succ2 {R α : Type*} [Semiring R] [TopologicalSpace α] [AddCommMonoid α]
    (f : R → α) : ∑' n : ℕ+, f n = ∑' (n : ℕ), f (n + 1) := by
  convert  (Equiv.pnatEquivNat.symm.tsum_eq _).symm
  simp

theorem sum_int_even {α : Type*} [UniformSpace α] [Ring α] [IsUniformAddGroup α] [CompleteSpace α]
  [T2Space α] (f : ℤ → α) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) :
    ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n := by
  rw [tsum_of_add_one_of_neg_add_one]
  · conv =>
      enter [1,2,1]
      ext n
      rw [hf]
    simp only [neg_add_rev, Int.reduceNeg, neg_neg, tsum_pnat_eq_tsum_succ2, two_mul]
    abel
  · simpa using ((summable_nat_add_iff (k := 1)).mpr (summable_int_iff_summable_nat_and_neg.mp hf2).1)
  · exact (summable_nat_add_iff (k := 1)).mpr (summable_int_iff_summable_nat_and_neg.mp hf2).2

lemma zeta_two_eqn (k : ℕ) (hk : 2 ≤ k) (hk2 : Even k) : ∑' (n : ℤ), ((n : ℂ) ^ k)⁻¹ =
    2 * riemannZeta k := by
  have hkk : 1 < (k ) := by
    linarith
  rw [sum_int_even]
  simp
  have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := by simp; omega
  norm_cast at *
  rw [h0]
  simp [zero_add, mul_eq_mul_left_iff]
  norm_cast
  simp only [PNat.pow_coe, Nat.cast_pow]
  rw [zeta_nat_eq_tsum_of_gt_one hkk, tsum_pnat_eq_tsum_succ2 (f := fun n => ((n : ℂ) ^ k)⁻¹) ]
  nth_rw 2 [Summable.tsum_eq_zero_add]
  simp
  omega
  apply Summable.of_norm
  simp only [one_div, norm_inv, norm_pow, Complex.norm_natCast, summable_nat_pow_inv, hkk]
  simp [Even.neg_pow hk2]
  apply Summable.of_norm
  apply Summable.of_nat_of_neg
  simp [hkk]
  simp [hkk]

theorem int_sum_neg {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (f : ℤ → α) :
    ∑' d, f (-d) = ∑' d, f d := by
  have h : (fun d => f (-d)) = (fun d => f d) ∘ (Equiv.neg ℤ) := by ext; simp
  rw [h]
  apply (Equiv.neg ℤ).tsum_eq

theorem s1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    Summable fun x : ℤ × ℤ ↦ 1 / (↑x.1 * (z : ℂ) + ↑x.2) ^ k := by
  apply Summable.of_norm
  rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
  apply (EisensteinSeries.summable_norm_eisSummand hk z).congr
  simp [EisensteinSeries.eisSummand]


lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
    ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z) ^ (n : ℕ) := by
  rw [← (piFinTwoEquiv fun _ => ℤ).symm.tsum_eq, Summable.tsum_prod (by apply s1 k hk), sum_int_even]
  · have (b : ℕ+) := Eisenstein_qExpansion_identity'' (k := k - 1) (by omega)
      ⟨b * z , by simpa using z.2⟩
    have hk1 : k - 1 + 1 = k := by omega
    simp only [Nat.ofNat_le_cast, coe_mk_subtype, hk1, one_div, neg_mul, mul_assoc, Fin.isValue,
      piFinTwoEquiv_symm_apply, Fin.cons_zero, Int.cast_zero, zero_mul, Fin.cons_one, zero_add,
      zeta_two_eqn k (by omega) hk2, Int.cast_natCast, add_right_inj, mul_eq_mul_left_iff,
      OfNat.ofNat_ne_zero, or_false] at *
    conv =>
      rw [← tsum_mul_left]
      enter [1,1]
      ext c
      rw [this c]
    simp_rw [tsum_mul_left, ← mul_assoc, tsum_sigma_eqn22 (k - 1) z]
  · intro n
    nth_rw 2 [(int_sum_neg _).symm]
    congr
    ext y
    simp only [Fin.isValue, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, ←
      Even.neg_pow hk2 (n * (z : ℂ) + y), neg_add_rev, one_div, Int.cast_neg, neg_mul, inv_inj]
    ring
  · simpa using Summable.prod (f := fun x : ℤ × ℤ => 1 / ((x.1 : ℂ) * z + x.2) ^ k)
      (by apply s1 k hk)


open Pointwise

def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 0

noncomputable def gammaSetN_map (N : ℕ) (v : gammaSetN N) : gammaSet 1 0 := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
  refine ⟨hv2.choose, hv2.choose_spec.1⟩

lemma gammaSet_top_mem (v : Fin 2 → ℤ)  : v ∈ gammaSet 1 0 ↔ IsCoprime (v 0) (v 1) := by
  simpa [gammaSet] using fun h ↦ Subsingleton.eq_zero (Int.cast ∘ v)

lemma gammaSetN_map_eq (N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetN_map N v := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
  exact (hv2.choose_spec.2).symm

noncomputable def gammaSetN_Equiv {N : ℕ} (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 0 where
  toFun v := gammaSetN_map N v
  invFun v := by
    use N • v
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    refine ⟨v, by simp⟩
  left_inv v := by
    simp_rw [← gammaSetN_map_eq N v]
  right_inv v := by
    have H : N • v.1 ∈ gammaSetN N := by
      simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
      refine ⟨v.1, by simp⟩
    simp [gammaSetN, mem_smul_set] at *
    let x := H.choose
    have hx := H.choose_spec
    have hxv : ⟨H.choose, H.choose_spec.1⟩ = v := by
      ext i
      simpa [hN] using (congr_fun H.choose_spec.2 i)
    simp_all only [gammaSetN_map]

lemma gammaSetN_eisSummand (k : ℤ) (z : ℍ) (n : ℕ) (v : gammaSetN n) : eisSummand k v z =
  ((n : ℂ) ^ k)⁻¹ * eisSummand k (gammaSetN_map n v) z := by
  simp only [eisSummand, gammaSetN_map_eq n v, Fin.isValue, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, zpow_neg, ← mul_inv]
  congr
  rw [← mul_zpow]
  ring_nf

private def Fin_to_GammaSetN (v : Fin 2 → ℤ) : Σ n : ℕ, gammaSetN n := by
  refine ⟨(v 0).gcd (v 1), ⟨(v 0).gcd (v 1) • ![(v 0)/(v 0).gcd (v 1), (v 1)/(v 0).gcd (v 1)], ?_⟩⟩
  by_cases hn : 0 < (v 0).gcd (v 1)
  · apply Set.smul_mem_smul (by aesop)
    rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
    apply Int.gcd_div_gcd_div_gcd hn
  · simp only [gammaSetN, Fin.isValue, (nonpos_iff_eq_zero.mp (not_lt.mp hn)), singleton_smul,
      Nat.succ_eq_add_one, Nat.reduceAdd, CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_nsmul]
    refine ⟨![1,1], by simpa [gammaSet_top_mem] using Int.isCoprime_iff_gcd_eq_one.mpr rfl⟩

def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (Σ n : ℕ, gammaSetN n) where
  toFun v := Fin_to_GammaSetN v
  invFun v := v.2
  left_inv v := by
            ext i
            fin_cases i
            · refine Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
            · refine Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))
  right_inv v := by
          ext i
          · have hv2 := v.2.2
            simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
            obtain ⟨x, hx⟩ := hv2
            simp [← hx.2, Fin_to_GammaSetN, Fin.isValue, Int.gcd_mul_left,
              Int.isCoprime_iff_gcd_eq_one.mp hx.1.2]
          · fin_cases i
            · refine Int.mul_ediv_cancel'  ?_
              simpa using Int.gcd_dvd_left _ _
            · refine Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)

lemma EQ22 {k : ℕ} (hk : 3 ≤ k) (z : ℍ) : ∑' (x : Fin 2 → ℤ), eisSummand k x z =
    (riemannZeta (k)) * ∑' (c : gammaSet 1 0), eisSummand k c z := by
  rw [← GammaSet_one_Equiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  rw [Summable.tsum_sigma, GammaSet_one_Equiv, zeta_nat_eq_tsum_of_gt_one hk1,
    tsum_mul_tsum_of_summable_norm (by simp [hk1])
    (by apply(EisensteinSeries.summable_norm_eisSummand (by omega) z).subtype)]
  · simp only [Equiv.coe_fn_symm_mk, one_div]
    rw [Summable.tsum_prod']
    · apply tsum_congr
      intro b
      by_cases hb : b = 0
      · simp [hb, CharP.cast_eq_zero, gammaSetN_eisSummand k z, show ((0 : ℂ) ^ k)⁻¹ = 0 by aesop]
      · simpa [gammaSetN_eisSummand k z, zpow_natCast, tsum_mul_left, hb] using
          (gammaSetN_Equiv hb).tsum_eq (fun v => eisSummand k v z)
    · apply summable_mul_of_summable_norm (f:= fun (n : ℕ)=> ((n : ℂ)^k)⁻¹ )
        (g := fun (v : (gammaSet 1 0) ) => eisSummand k v z) (by simp [hk1])
      apply (EisensteinSeries.summable_norm_eisSummand (by omega) z).subtype
    · intro b
      simpa using (Summable.of_norm (by apply (EisensteinSeries.summable_norm_eisSummand
        (by omega) z).subtype)).mul_left (a := ((b : ℂ) ^ k)⁻¹)
  · apply ((GammaSet_one_Equiv.symm.summable_iff (f := fun v => eisSummand k v z)).mpr
      (EisensteinSeries.summable_norm_eisSummand (by omega) z).of_norm).congr
    simp

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

open ModularForm

/-- Normalised Eisenstein series, here they need  `1/2` since we sum over coprime pairs. -/
noncomputable def ModularForm.E (k : ℕ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF (by omega) standardcongruencecondition

lemma E_k_q_expansion {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 + (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
    ∑' n : ℕ+, sigma (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) := by
  have : (eisensteinSeries_MF (k := k) (by omega) standardcongruencecondition) z =
    (eisensteinSeries_SIF standardcongruencecondition k) z := rfl
  rw [E, ModularForm.smul_apply, this, eisensteinSeries_SIF_apply standardcongruencecondition k z,
    eisensteinSeries, standardcongruencecondition]
  have HE1 := EQ1 k (by omega) hk2 z
  have HE2 := EQ22 (by omega) z
  have z2 : (riemannZeta (k)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp only [natCast_re, Nat.one_lt_cast]
    omega
  simp only [PNat.val_ofNat, Fin.isValue, UpperHalfPlane.coe, one_div, neg_mul, ←
    inv_mul_eq_iff_eq_mul₀ z2, ne_eq, eisSummand, zpow_neg, zpow_natCast, smul_eq_mul] at *
  simp_rw [← HE2, ← mul_assoc, HE1, mul_add]
  field_simp
  ring
