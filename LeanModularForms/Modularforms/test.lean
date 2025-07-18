import Mathlib

@[to_additive]
theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α] [DecidableEq ι]
    (s : Set β) {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s := by
  intro t ht
  simp only [Finset.prod_apply] at *
  congr
  exact funext fun i ↦ h i ht

@[to_additive]
theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α] [DecidableEq ι]
    (s : Set β) {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  intro t ht
  simp only at *
  congr
  exact funext fun i ↦ h i ht

#find_home eqOn_fun_finsetProd
