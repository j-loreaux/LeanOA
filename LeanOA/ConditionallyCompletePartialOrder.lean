import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Order.MonotoneConvergence


section ConditionallyCompletePartialOrder

variable {ι : Sort*} {α : Type*}

/-- Conditionally complete partial orders (with suprema) are partial orders
where every nonempty, directed set which is bounded above has a least upper bound. -/
class ConditionallyCompletePartialOrderSup (α : Type*)
    extends PartialOrder α, SupSet α where
  /-- For each nonempty, directed set `s` which is bounded above, `sSup s` is
  the least upper bound of `s`. -/
  isLUB_csSup_of_directed :
    ∀ s, DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s → IsLUB s (sSup s)

/-- Conditionally complete partial orders (with infima) are partial orders
where every nonempty, directed set which is bounded below has a greatest lower bound. -/
class ConditionallyCompletePartialOrderInf (α : Type*)
    extends PartialOrder α, InfSet α where
  /-- For each nonempty, directed set `s` which is bounded below, `sInf s` is
  the greatest lower bound of `s`. -/
  isGLB_csInf_of_directed :
    ∀ s, DirectedOn (· ≥ ·) s → s.Nonempty → BddBelow s → IsGLB s (sInf s)

/-- Conditionally complete partial orders (with suprema and infimae) are partial orders
where every nonempty, directed set which is bounded above (respectively, below) has a
least upper (respectively, greatest lower) bound. -/
class ConditionallyCompletePartialOrder (α : Type*)
    extends ConditionallyCompletePartialOrderSup α, ConditionallyCompletePartialOrderInf α where

section Sup

variable [ConditionallyCompletePartialOrderSup α]
variable {f : ι → α} {s : Set α} {a : α}

protected lemma DirectedOn.isLUB_csSup (h_dir : DirectedOn (· ≤ ·) s)
    (h_non : s.Nonempty) (h_bdd : BddAbove s) : IsLUB s (sSup s) :=
  ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed s h_dir h_non h_bdd

protected lemma DirectedOn.le_csSup (hs : DirectedOn (· ≤ ·) s)
    (h_bdd : BddAbove s) (ha : a ∈ s) : a ≤ sSup s :=
  (hs.isLUB_csSup ⟨a, ha⟩ h_bdd).1 ha

protected lemma DirectedOn.csSup_le (hd : DirectedOn (· ≤ ·) s) (h_non : s.Nonempty)
    (ha : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (hd.isLUB_csSup h_non ⟨a, ha⟩).2 ha

protected lemma Directed.le_ciSup (hf : Directed (· ≤ ·) f)
    (hf_bdd : BddAbove (Set.range f)) (i : ι) : f i ≤ ⨆ j, f j :=
  hf.directedOn_range.le_csSup  hf_bdd <| Set.mem_range_self _

protected lemma Directed.ciSup_le [Nonempty ι] (hf : Directed (· ≤ ·) f)
    (ha : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
hf.directedOn_range.csSup_le (Set.range_nonempty _) <| Set.forall_mem_range.2 ha

end Sup

section Inf

variable [ConditionallyCompletePartialOrderInf α]
variable {f : ι → α} {s : Set α} {a : α}

protected lemma DirectedOn.isGLB_csInf (h_dir : DirectedOn (· ≥ ·) s)
    (h_non : s.Nonempty) (h_bdd : BddBelow s) : IsGLB s (sInf s) :=
  ConditionallyCompletePartialOrderInf.isGLB_csInf_of_directed s h_dir h_non h_bdd

protected lemma DirectedOn.le_csInf (hs : DirectedOn (· ≥ ·) s)
    (h_bdd : BddBelow s) (ha : a ∈ s) : sInf s ≤ a :=
  (hs.isGLB_csInf ⟨a, ha⟩ h_bdd).1 ha

protected lemma DirectedOn.csInf_le (hd : DirectedOn (· ≥ ·) s) (h_non : s.Nonempty)
    (ha : ∀ b ∈ s, a ≤ b) : a ≤ sInf s :=
  (hd.isGLB_csInf h_non ⟨a, ha⟩).2 ha

protected lemma Directed.le_ciInf (hf : Directed (· ≥ ·) f)
    (hf_bdd : BddBelow (Set.range f)) (i : ι) : ⨅ j, f j ≤ f i :=
  hf.directedOn_range.le_csInf  hf_bdd <| Set.mem_range_self _

protected lemma Directed.ciInf_le [Nonempty ι] (hf : Directed (· ≥ ·) f)
    (ha : ∀ i, a ≤ f i) : a ≤ ⨅ i, f i :=
hf.directedOn_range.csInf_le (Set.range_nonempty _) <| Set.forall_mem_range.2 ha

end Inf

--TODO: We could mimic more `sSup`/`iSup` lemmas

instance ConditionallyCompleteLattice.toConditionallyCompletePartialOrder {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompletePartialOrder α where
  isLUB_csSup_of_directed _ _ h_non h_bdd := isLUB_csSup h_non h_bdd
  isGLB_csInf_of_directed _ _ h_non h_bdd := isGLB_csInf h_non h_bdd

--- these are unidirectional
instance CompletePartialOrder.toConditionallyCompletePartialOrderSup {α : Type*}
    [CompletePartialOrder α] : ConditionallyCompletePartialOrderSup α where
  isLUB_csSup_of_directed _ h_dir _ _ := h_dir.isLUB_sSup

namespace OrderDual

instance {α : Type*} [ConditionallyCompletePartialOrderSup α] :
    ConditionallyCompletePartialOrderInf (OrderDual α) where
  isGLB_csInf_of_directed _ h_dir h_non h_bdd := h_dir.isLUB_csSup (α := α) h_non h_bdd

instance {α : Type*} [ConditionallyCompletePartialOrderInf α] :
    ConditionallyCompletePartialOrderSup (OrderDual α) where
  isLUB_csSup_of_directed _ h_dir h_non h_bdd := h_dir.isGLB_csInf (α := α) h_non h_bdd

instance {α : Type*} [ConditionallyCompletePartialOrder α] :
    ConditionallyCompletePartialOrder (OrderDual α) where

end OrderDual


end ConditionallyCompletePartialOrder

section Convergence

-- these are simply generalizations of the existing ones for lattices.
-- they can be outright replaced.

open Filter Set
open scoped Topology

variable {ι α β : Type*} [Preorder ι]

section Sup

variable [TopologicalSpace α] [ConditionallyCompletePartialOrderSup α] [SupConvergenceClass α]
variable {f : ι → α}

theorem tendsto_atTop_ciSup' (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
    exact tendsto_atTop_isLUB h_mono <|
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

theorem tendsto_atBot_ciSup' (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by
  convert tendsto_atTop_ciSup' h_anti.dual hbdd.dual using 1

end Sup

section Inf

variable [TopologicalSpace α] [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α]
variable {f : ι → α}

theorem tendsto_atBot_ciInf' (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by
  convert tendsto_atTop_ciSup' h_mono.dual hbdd.dual using 1

theorem tendsto_atTop_ciInf' (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by
  convert tendsto_atBot_ciSup' h_anti.dual hbdd.dual using 1

end Inf

-- these ones below can be replaced in Mathlib *immeditately*. It's just a type class change.

theorem Monotone.ge_of_tendsto' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

theorem Monotone.le_of_tendsto' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual.ge_of_tendsto' ha b

theorem Antitone.le_of_tendsto' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual_right.ge_of_tendsto' ha b

theorem Antitone.ge_of_tendsto' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  hf.dual_right.le_of_tendsto' ha b

theorem isLUB_of_tendsto_atTop' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto' ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem isGLB_of_tendsto_atBot' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a :=
  isLUB_of_tendsto_atTop' (α := αᵒᵈ) (β := βᵒᵈ) hf.dual ha

theorem isLUB_of_tendsto_atBot' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a :=
  isLUB_of_tendsto_atTop' (α := α) (β := βᵒᵈ) hf.dual_left ha

theorem isGLB_of_tendsto_atTop' [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Nonempty β] [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a :=
  isGLB_of_tendsto_atBot' (α := α) (β := βᵒᵈ) hf.dual_left ha

end Convergence
