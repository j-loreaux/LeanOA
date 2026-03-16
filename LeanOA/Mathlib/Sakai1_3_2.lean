import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Category.Stonean.Basic

variable {K} [TopologicalSpace K]

open ContinuousFunctions NNReal

-- This can work inline, but may be good for Mathlib.
lemma isClosed_of_closure_int_compl {A : Set K} : IsClosed A ↔ closure A ∩ Aᶜ = ∅ :=
  ⟨fun _ ↦ by simp, fun H ↦ closure_subset_iff_isClosed.mp <| Set.diff_eq_empty.mp H⟩

lemma aux {A : Set K} : ¬ IsClosed A ↔ closure A ∩ Aᶜ ≠ ∅ := by
  simp only [isClosed_of_closure_int_compl, ne_eq]

variable [T2Space K] [CompactSpace K]

/- Temporarily removed ℝ≥0 everywhere in order to access Urysohn from Mathlib. -/
theorem ExtremallyDisconnected_of_notSureWhatYet
    : (∀ s : Set C(K, ℝ), DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s →
    ∃ (g : C(K, ℝ)), IsLUB s g) → ExtremallyDisconnected K := fun H1 ↦ by
  constructor
  intro U hU
  by_contra H2
  obtain ⟨t, ht⟩ : Nonempty U := by
    grind [not_nonempty_iff, Set.isEmpty_coe_sort, closure_empty]
  -- The following obtain and have should be made a lemma somehow.
  obtain ⟨w, hw0, hw1, hwIcc⟩ := exists_continuous_zero_one_of_isClosed
      (X := K) (t := {t}) (s := Uᶜ) (by aesop) (by aesop) (by aesop)
  have hwsupportmem : w ∈ {f : C(K, ℝ) | (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ Uᶜ, f x = 0)} := by
    constructor
    · exact hwIcc
    · exact fun x a ↦ (fun {x} ↦ EReal.coe_eq_zero.mp) (congrArg Real.toEReal (hw0 a))
  have hR : DirectedOn (· ≤ ·) {f : C(K, ℝ) | (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ Uᶜ, f x = 0)}
      := by
    sorry
  obtain ⟨g, hg⟩ := H1 {f : C(K, ℝ) | (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ Uᶜ, f x = 0)}
    hR ⟨w, Set.mem_setOf.mpr hwsupportmem⟩
    ⟨1, fun f Hf x ↦ (Hf.1 x).2⟩
  have Last : Set.EqOn g 0 (closure U)ᶜ := by
    have Bga := hg.2
    dsimp [lowerBounds, upperBounds] at Bga
    simp only [Set.mem_compl_iff, and_imp] at Bga
    have := Bga (a := (0 : C(K, ℝ)))
    sorry
  have heqonclos: ∀ x ∈ closure U, Set.EqOn g (fun x => 1) (closure U) := fun x hx ↦ by
    apply ContinuousWithinAt.eqOn_const_closure (X := K) (Y := ℝ) (c := 1) (s := U) (f := g)
    · exact fun y hy ↦ map_continuousWithinAt g U y
    · exact Set.EqOn.symm <| fun r hrU ↦ by
        apply le_antisymm
        · obtain ⟨v, hv0, hv1, hvIcc⟩ := exists_continuous_zero_one_of_isClosed
            (X := K) (t := {r}) (s := Uᶜ) (by aesop) (by aesop) (by aesop)
          have hvsupmem : v ∈ {f : C(K, ℝ) | (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ Uᶜ, f x = 0)} := by
            constructor
            · exact hvIcc
            · exact fun x a ↦ (fun {x} ↦ EReal.coe_eq_zero.mp) (congrArg Real.toEReal (hv0 a))
          have : v r ≤ g r := by
            have := (hg.1 <| Set.mem_setOf.mpr hvsupmem) r
            simp only [ContinuousMap.toFun_eq_coe] at this
            exact RCLike.ofReal_le_ofReal.mp this
          rwa [hv1, Pi.one_apply] at this
          exact Set.mem_singleton r
        · have : (1 : C(K, ℝ)) ∈ upperBounds
            {f : C(K, ℝ) | (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ Uᶜ, f x = 0)} :=
          fun a ha ↦ fun x ↦ ((fun a ↦ (ha.1 x).2) ∘ U) t
          exact RCLike.ofReal_le_ofReal.mp (hg.2 this r)
  have heqonc : Set.EqOn w 0 (closure U)ᶜ := fun ⦃x⦄ a ↦ hw0 <|
      (Set.compl_subset_compl_of_subset <| subset_closure) a
  have hTra : ¬ IsClosed (closure U)ᶜ := by simpa [isClosed_compl_iff]
  have hRLe: w t ≤ g t := (hg.1 <| Set.mem_setOf.mpr hwsupportmem) t
  rw [hw1, Pi.one_apply] at hRLe
  · simp only [isClosed_of_closure_int_compl, compl_compl] at hTra
    · push_neg at hTra
      obtain ⟨s, hs⟩ := hTra
      simp only [Set.mem_inter_iff] at hs
      have cont_clos : g '' (closure (closure U)ᶜ) ⊆ closure (g '' ((closure U)ᶜ)) := by
          have : Continuous g := ContinuousMap.continuous g
          rw [continuous_iff_image_closure_subset_closure_image (f := g)] at this
          exact LE.le.subset (this (closure U)ᶜ)
      have one_eq : 1 = g s :=
        Eq.symm ((fun {x} ↦ EReal.coe_eq_one.mp) (congrArg Real.toEReal (heqonclos s hs.2 hs.2)))
      have haux : g '' (closure U)ᶜ ⊆ {0} := by
        intro y hy
        simp only [Set.mem_image, Set.mem_compl_iff] at hy
        obtain ⟨i, hi⟩ := hy
        have : i ∉ closure U → i ∈ Uᶜ := by
          contrapose
          simp only [Set.mem_compl_iff, not_not]
          apply subset_closure (X := K)
        simp only [Set.mem_singleton_iff]
        have : g i = 0 := by grind [(Set.mem_compl_iff (closure U) i).mpr hi.1]
        rwa [← hi.2]
      have st := subset_trans cont_clos (closure_mono haux)
      simp only [Set.finite_singleton, Set.Finite.isClosed, IsClosed.closure_eq,
        Set.subset_singleton_iff, Set.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at st
      have := Eq.trans one_eq ((fun {x} ↦ EReal.coe_eq_zero.mp) (congrArg Real.toEReal (st s hs.1)))
      simpa
  · exact Set.mem_singleton t
