/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
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
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x => ∑' n, f n x) {s} :=  by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn_of_cofinite_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x => ∑' n, f n x) {s} := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    (f : α → β → F) {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := (fun x => ∑' i, f i x))
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  apply tendstoUniformlyOn_tsum hu1 fun n x hx ↦ hu2 n ⟨x, hx⟩

/-- The `derivWithin` of a absolutely and uniformly converget sum on an open set `s` is the sum
of the derivatives of squence of functions on the open set `s` -/
theorem derivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] (f : α → E → F) {s : Set E}
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n , f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (IsOpen.uniqueDiffWithinAt hs hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ Summable.hasSum (hf y hy)) hx
    (f' := fun n : Finset α ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ Eq.symm (HasSumLocallyUniformlyOn.tsum_eqOn hg hb)
  · filter_upwards with t r hr
    apply HasDerivAt.fun_sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · exact DifferentiableWithinAt.hasDerivWithinAt (hf2 q r hr).differentiableWithinAt
    · exact IsOpen.mem_nhds hs hr

lemma tsum_eq_summable {ι α : Type*} [AddCommMonoid α] [ TopologicalSpace α]
    (g : ι → α) (h : ∑' n, g n ≠ 0) :
    Summable g := by
  by_contra hg
  rw [tsum_eq_zero_of_not_summable hg] at h
  aesop

variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α} {𝔖 : Set (Set β)}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α] [TopologicalSpace β] [T2Space α] [DecidableEq ι]

@[to_additive]
theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α] [DecidableEq ι]
    (s : Set β) (f f' : ι → β → α) (h : ∀ (i : ι), EqOn (f i) (f' i) s) (v : Finset ι) :
    EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s := by
  intro t ht
  simp only [Finset.prod_apply] at *
  congr
  exact funext fun i ↦ h i ht

@[to_additive]
theorem eqOn_finsetProd_fun {ι α β : Type*} [CommMonoid α] [DecidableEq ι]
    (s : Set β) (f f' : ι → β → α) (h : ∀ (i : ι), EqOn (f i) (f' i) s) (v : Finset ι) :
    EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  intro t ht
  simp only at *
  congr
  exact funext fun i ↦ h i ht

@[to_additive]
lemma MultipliableLocallyUniformlyOn_congr (f f' : ι → β → α) (h : ∀ i,  s.EqOn (f i)  (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  apply (h2.hasProdLocallyUniformlyOn).congr fun v ↦ eqOn_finsetProd_fun s f f' h v

theorem iteratedDerivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] (f : ι → E → F) {s : Set E}
    (m : ℕ) (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (h : ∀ k, k ≤ m → SummableLocallyUniformlyOn (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, k ≤ m → r ∈ s → DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n , f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction' m with m hm generalizing x
  · simp
  · simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum _ hs hx]
    · apply derivWithin_congr
      · exact fun t ht => hm ht (fun k hk => h k (by omega)) (fun k r e hr he => hf2 k r e (by omega) he)
      · exact hm hx (fun k hk => h k (by omega)) (fun k r e hr he => hf2 k r e (by omega) he)
    · exact fun y hy => ((h m (by omega)).summable hy).congr (fun _ => by simp)
    · exact SummableLocallyUniformlyOn_congr _ _ (fun i ⦃t⦄ ht ↦ iteratedDerivWithin_succ) (h (m + 1) (by rfl))
    · exact fun n r hr ↦ hf2 n m r (by omega) hr

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}

section

include h hx in
theorem iteratedDerivWithin_fun_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun z => f z + g z) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simpa using iteratedDerivWithin_add hx h hf hg

theorem iteratedDerivWithin_univ_zpow (m : ℤ) (k : ℕ) :
    iteratedDerivWithin k (fun y => y ^ m) univ =
    fun y => (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k) := by
  rw [iteratedDerivWithin_univ, iteratedDeriv_eq_iterate]
  simp

theorem iteratedDerivWithin_of_isOpen (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  unfold iteratedDerivWithin iteratedDeriv
  intro x hx
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := 𝕜) (F := F) (E := 𝕜) (f := f) n hs hx]


theorem iteratedDerivWithin_congr_of_isOpen (f : 𝕜 → F) (n : ℕ) (s t : Set 𝕜) (hs : IsOpen s) (ht : IsOpen t) :
   (s ∩ t).EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n f t) := by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs (f := f) (n := n) hr.1,
    iteratedDerivWithin_of_isOpen ht (f := f) (n := n) hr.2]

theorem iteratedDerivWithin_of_isOpen_eq_iterate (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (deriv^[n] f) s := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  exact fun ⦃x⦄ ↦ congrFun rfl

theorem iteratedDerivWithin_zpow (m : ℤ) (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y => y ^ m) s)
    (fun y => (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k)) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

theorem iteratedDerivWithin_one_div (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y => 1 / y) s)
    (fun y => (-1) ^ k * (k !) * (1 / y ^ (k + 1))) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  simp only [one_div, iter_deriv_inv', Int.reduceNeg]
  intro t ht
  rw [show -1 -(k : ℤ) = -(k + 1) by ring]
  norm_cast
  simp

theorem iter_deriv_inv_linear (k : ℕ) (c d : 𝕜) :
    deriv^[k] (fun x => (d * x + c)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * d ^ k * (d * x + c)^ (-1 - k : ℤ)) := by
  induction' k with k ihk
  · simp
  · rw [Nat.factorial_succ, show  k + 1 = 1 + k by ring, @iterate_add_apply, ihk]
    ext z
    simp only [Int.reduceNeg, iterate_one, deriv_const_mul_field',
      Nat.cast_add, Nat.cast_one]
    by_cases hd : d = 0
    · rw [hd]
      simp
    · have := deriv_comp_add_const (fun x => (d * x) ^ (-1 - k : ℤ)) (c / d) z
      have h0 : (fun x ↦ (d * (x + c / d)) ^ (-1 - (k : ℤ))) = (fun x ↦ (d * x + c) ^ (-1 - (k : ℤ))) := by
        ext y
        field_simp
        ring_nf
      rw [h0, deriv_comp_mul_left d (fun x ↦ (x) ^ (-1 - k : ℤ)) (z + c / d)] at this
      rw [this]
      field_simp
      ring_nf

local notation "ℂ_ℤ " => Complex.integerComplement

  theorem contDiffOn_inv_linear (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z + d)) ℂ_ℤ := by
  simp only [one_div]
  apply ContDiffOn.inv
  fun_prop
  exact fun x hx => Complex.integerComplement_add_ne_zero hx d

 theorem contDiffOn_inv_linear_sub (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d)) ℂ_ℤ := by
  simp_rw [sub_eq_add_neg]
  convert contDiffOn_inv_linear (-d) k
  simp




lemma cotTerm_iteratedDeriv (d k : ℕ) : EqOn (iteratedDeriv k (fun (z : ℂ) => cotTerm z d))
    (fun z : ℂ => (-1) ^ k * k ! * (1 / (z + (d + 1)) ^ (k + 1) + 1 / (z - (d + 1)) ^ (k + 1) )) ℂ_ℤ := by
  intro z hz
  simp_rw [cotTerm]
  have h1 :
    (fun z : ℂ => 1 / (z - (d + 1)) + 1 / (z + (d + 1))) =
      (fun z : ℂ => 1 / (z - (d + 1))) + fun z : ℂ => 1 / (z + (d +1)) := by rfl
  rw [h1, iteratedDeriv_add  ?_]
  · simp only [one_div, iteratedDeriv_eq_iterate, sub_eq_add_neg]
    have h2 := iter_deriv_inv_linear k (-(d + 1 : ℂ)) 1
    have h3 := iter_deriv_inv_linear k (d + 1 : ℂ) 1
    simp only [one_div, one_mul, neg_add_rev, one_pow,
      mul_one, Int.reduceNeg] at *
    simp_rw [h2, h3, show -1 -(k : ℤ) = -(k + 1) by ring, show (k : ℤ) + 1 = ((k + 1) : ℕ) by simp,
      zpow_neg, ← inv_pow, ← inv_zpow, zpow_natCast ]
    ring
  · simpa using (contDiffOn_inv_linear (d + 1) k).contDiffAt
      (IsOpen.mem_nhds ( (by apply Complex.isOpen_compl_range_intCast)) hz)
  · simpa using (contDiffOn_inv_linear_sub (d + 1) k).contDiffAt
      (IsOpen.mem_nhds ( (by apply Complex.isOpen_compl_range_intCast)) hz)

lemma cotTerm_iteratedDerivWith (d k : ℕ) : EqOn (iteratedDerivWithin k (fun (z : ℂ) => cotTerm z d) ℂ_ℤ)
    (fun z : ℂ => (-1) ^ k * k ! * (1 / (z + (d + 1)) ^ (k + 1) + 1 / (z - (d + 1)) ^ (k + 1) )) ℂ_ℤ := by
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
    (iteratedDerivWithin k (fun (z : ℂ) => cotTerm z d) {z : ℂ | 0 < z.im})
    (fun z : ℂ => (-1) ^ k * k ! * (1 / (z + (d + 1)) ^ (k + 1) + 1 / (z - (d + 1)) ^ (k + 1) ))
    {z : ℂ | 0 < z.im} := by
  have h1 : IsOpen ℂ_ℤ := by apply Complex.isOpen_compl_range_intCast
  have := iteratedDerivWithin_congr_of_isOpen (fun (z : ℂ) => cotTerm z d) k _ _
    UpperHalPlane_isOpen h1
  rw [upperHalfPlane_inter_integerComplement] at this
  apply Set.EqOn.trans this
  intro z hz
  simpa using  cotTerm_iteratedDerivWith d k (UpperHalfPlane.coe_mem_integerComplement ⟨z,hz⟩)

lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm (d k : ℕ) :
    SummableLocallyUniformlyOn
    (fun n : ℕ ↦ iteratedDerivWithin k (fun z : ℂ => cotTerm z d) {z : ℂ | 0 < z.im})
      {z : ℂ | 0 < z.im} := by
  sorry

theorem aux_iter_der_tsum'' (k : ℕ) (hk : 1 ≤ k) (x : ℍ) :
    iteratedDerivWithin k
        ((fun z : ℂ => 1 / z) + fun z : ℂ => ∑' n : ℕ, cotTerm z n) {z : ℂ | 0 < z.im}  x =
      (-1) ^ (k : ℕ) * (k : ℕ)! * ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ (k + 1 : ℕ) := by

  rw [iteratedDerivWithin_add ?_ ?_]
  · have := iteratedDerivWithin_tsum (fun (n : ℕ) z => cotTerm z n) (s :=  {z : ℂ | 0 < z.im}) k
    rw [this]
    rw [iteratedDerivWithin_one_div]
    have hx : UpperHalfPlane.coe x ∈ {z : ℂ | 0 < z.im} := by
      simp [UpperHalfPlane.coe]
    conv =>
      enter [1,2,1]
      ext n
      rw [cotTerm_iteratedDerivWith' n k hx]
    simp
    rw [tsum_of_add_one_of_neg_add_one]
    rw [tsum_mul_left, Summable.tsum_add]
    simp_rw [sub_eq_add_neg]
    simp
    ring
    apply  ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
      (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by omega))).1).congr
    intro n
    norm_cast
    ring
    apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
      (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by omega))).2).congr
    intro n
    simp
    norm_cast
    congr
    simp
    ring







    sorry




    all_goals{sorry}
  all_goals {sorry}

/- lemma derivWithin_SummableUniformlyOn_eq {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] {f g : α → E → F} {s : Set E}
    (hs : IsOpen s) (hf0 : ∀ y ∈ s, Summable fun n ↦ f n y)
    (hg0 :  ∀ y ∈ s, Summable fun n ↦ g n y)
    (hf : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hg : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ g n z) s)) s)
    (hfg :s.EqOn (∑' n, f n) (∑' n, g n))
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r)
    (hg2 : ∀ n r, r ∈ s → DifferentiableAt E (g n) r)  :
    s.EqOn (∑' n,  (derivWithin (f n) s))  (∑' n,  (derivWithin (g n) s)) := by
  intro z hz
  have := derivWithin_tsum f hs hz hf0 hf hf2
  rw [tsum_apply, ← this]
  have := derivWithin_tsum g hs hz hg0 hg hg2
  rw [tsum_apply, ← this]
  apply derivWithin_congr
  intro t ht
  have H := hfg ht
  simp
  rw [tsum_apply, tsum_apply] at H
  exact H
  all_goals {sorry} -/
