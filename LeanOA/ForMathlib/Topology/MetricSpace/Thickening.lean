import Mathlib.Topology.MetricSpace.Thickening

open Metric

lemma IsClopen.of_thickening_subset_self {α : Type*} [PseudoMetricSpace α] {s : Set α}
    {δ : ℝ} (hδ : 0 < δ) (hs : thickening δ s ⊆ s) :
    IsClopen s := by
  replace hs : thickening δ s = s := le_antisymm hs (self_subset_thickening hδ s)
  refine ⟨?_, hs ▸ isOpen_thickening⟩
  rw [← closure_subset_iff_isClosed, closure_eq_iInter_thickening]
  exact Set.biInter_subset_of_mem hδ |>.trans_eq hs
