import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

lemma CStarAlgebra.prod_nonneg_of_commute {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {l : List A} (hl_nonneg : ∀ x ∈ l, 0 ≤ x) (hl_comm : ∀ x ∈ l, ∀ y ∈ l, Commute x y) :
    0 ≤ l.prod := by
  induction l with
  | nil => exact zero_le_one
  | cons x xs ih =>
    simp only [List.prod_cons]
    simp only [List.mem_cons, forall_eq_or_imp, Commute.refl, true_and] at hl_nonneg hl_comm
    refine Commute.list_prod_right _ _ hl_comm.1 |>.mul_nonneg hl_nonneg.1 ?_
    refine ih hl_nonneg.2 ?_
    peel hl_comm.2 with x hx _
    exact this.2
