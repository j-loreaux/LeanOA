module

public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

open scoped Topology
open Set Filter

lemma nhdsGT_basis_Ioc {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] (a : α) :
    (𝓝[>] a).HasBasis (fun x ↦ a < x) (Ioc a) := nhdsGT_basis a |>.to_hasBasis'
  (fun _ hac ↦
    have ⟨b, hab, hbc⟩ := exists_between hac
    ⟨b, hab, Ioc_subset_Ioo_right hbc⟩)
  fun _ hac ↦ mem_of_superset ((nhdsGT_basis a).mem_of_mem hac) Ioo_subset_Ioc_self
