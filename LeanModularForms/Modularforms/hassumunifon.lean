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

open Set Metric TopologicalSpace Function Filter

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
    (h : ∀ k, SummableLocallyUniformlyOn (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, r ∈ s → DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n , f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction' m with m hm generalizing x
  · simp
  · simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum _ hs hx]
    · exact derivWithin_congr (fun _ ht ↦ hm ht) (hm hx)
    · exact fun y hy => ((h m).summable hy).congr (fun _ => by simp)
    · exact SummableLocallyUniformlyOn_congr _ _ (fun i ⦃t⦄ ht ↦ iteratedDerivWithin_succ) (h (m+1))
    · exact fun n r hr ↦ hf2 n m r hr


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


theorem iteratedDerivWithin_zpow (m : ℤ) (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y => y ^ m) s)
    (fun y => (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k)) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  intro t ht
  simp

theorem iteratedDerivWithin_one_div (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y => 1 / y) s)
    (fun y => (-1) ^ k * (k !) * (1 / y ^ (k + 1))) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  simp only [iteratedDeriv_eq_iterate, one_div, iter_deriv_inv', Int.reduceNeg]
  intro t ht
  rw [show -1 -(k : ℤ) = -(k + 1) by ring]
  norm_cast
  simp

@[simp]
theorem iter_deriv_inv'' (k : ℕ) (c : 𝕜) :
    deriv^[k] (fun x => (x + c)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * (x + c)^ (-1 - k : ℤ)) := by
  induction' k with k ihk
  simp
  rw [show  k + 1 = 1 + k by ring]
  rw [@iterate_add_apply, ihk]
  ext z
  by_cases hzc : z + c = 0
  simp [hzc]


  sorry
  simp
  have h0 : (fun x ↦ (x + c) ^ (-1 - (k : ℤ))) = (fun x => x ^ (-(1 + k : ℤ))) ∘ (fun x => x + c) := by
    ext z
    grind
  rw [h0, deriv_comp]
  simp


  sorry
  rw [differentiableAt_zpow]
  aesop
  simp

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedDerivWithin_comp_const_add (n : ℕ) (f : 𝕜 → F)  :
    iteratedDerivWithin n (fun z ↦ f (x + z)) s = fun t ↦ (iteratedDerivWithin n f (x +ᵥ s) (x + t)) := by
  induction n with
  | zero => simp only [iteratedDerivWithin_zero]
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ]


    sorry

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedDeriv_comp_add_const (n : ℕ) (f : 𝕜 → F) (s : 𝕜) :
    iteratedDeriv n (fun z ↦ f (z + s)) = fun t ↦ iteratedDeriv n f (t + s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_add_const _ s

local notation "ℂ_ℤ " => Complex.integerComplement

lemma cotTerm_iteratedDerivWith (d k : ℕ) : EqOn (iteratedDerivWithin k (fun (z : ℂ) => cotTerm z d) ℂ_ℤ)
    (fun z : ℂ => (-1) ^ k * k ! * (1 / (z + d) ^ (k + 1) + 1 / (z - d) ^ (k + 1) )) ℂ_ℤ := by
  intro z hz
  simp_rw [cotTerm]
  have h1 :
    (fun z : ℂ => 1 / (z - (d + 1)) + 1 / (z + (d + 1))) =
      (fun z : ℂ => 1 / (z - (d + 1))) + fun z : ℂ => 1 / (z + (d +1)) :=
    by  rfl
  rw [h1]
  rw [iteratedDerivWithin_add hz ?_]
  sorry




theorem aut_iter_deriv (d k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  induction' k with k IH generalizing x
  simp only [iteratedDerivWithin_zero, pow_zero, Nat.factorial_zero, one_mul]
  simp  at *
  rw [iteratedDerivWithin_succ]
  simp only [one_div, Nat.cast_succ, Nat.factorial, Nat.cast_mul]
  have := (IH hx)
  have H : derivWithin (fun (z : ℂ) => (-1: ℂ) ^ k * ↑k ! * ((z + ↑d) ^ (k + 1))⁻¹) {z : ℂ | 0 < z.im} x =
   (-1) ^ (↑k + 1) * ((↑k + 1) * ↑k !) * ((x + ↑d) ^ (↑k + 1 + 1))⁻¹ := by
    rw [DifferentiableAt.derivWithin]
    · simp only [deriv_const_mul_field']


      have h0 : (fun z : ℂ => ((z + d) ^ (k + 1))⁻¹) = (fun z : ℂ => (z + d) ^ (k + 1))⁻¹ := by
        rfl
      rw [h0]
      have h1 : (fun z : ℂ => ((z + d) ^ (k + 1))) = (fun z : ℂ => (z + d)) ^ (k + 1) := by
        rfl
      rw [h1]
      rw [deriv_inv'', deriv_pow'', deriv_add_const', deriv_id'']
      simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, mul_one]
      rw [pow_add]
      simp [pow_one]

      have Hw : (-(((k : ℂ) + 1) * (x + ↑d) ^ k) / ((x + ↑d) ^ k * (x + ↑d)) ^ 2) = -(↑k + 1) / (x + ↑d) ^ (k + 2) :=
        by
        rw [div_eq_div_iff]
        norm_cast
        simp
        ring
        norm_cast
        apply pow_ne_zero
        apply mul_ne_zero
        apply pow_ne_zero k (upper_ne_int ⟨x, hx⟩ d)
        apply upper_ne_int ⟨x, hx⟩ d
        norm_cast
        apply pow_ne_zero (k + 2) (upper_ne_int ⟨x, hx⟩ d)
      rw [Hw]
      ring
      fun_prop
      fun_prop
      norm_cast
      apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
    · apply DifferentiableAt.mul
      · fun_prop
      · apply DifferentiableAt.inv
        fun_prop
        apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
    · apply IsOpen.uniqueDiffWithinAt _ hx
      refine isOpen_lt ?_ ?_
      · fun_prop
      · fun_prop
  rw [←H]
  apply derivWithin_congr
  norm_cast at *
  simp at *
  intro r hr
  apply IH hr
  norm_cast at *
  simp at *
  apply this



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
