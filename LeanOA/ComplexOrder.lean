import Mathlib.Analysis.Complex.Basic
import LeanOA.ConditionallyCompletePartialOrder

/-
There's still a lot of API missing here.
-/

namespace Complex

open scoped ComplexOrder

/-- Given a nonempty set in `ℂ` which is bounded above, all the elements in the set must have
the same imaginary part (because they are all comparable to fixed) -/
noncomputable instance : SupSet ℂ where
  sSup s := open Classical in
    if h : s.Nonempty ∧ BddAbove s then sSup (re '' s) + im h.1.choose * I else 0

lemma sSup_def {s : Set ℂ} (hs : s.Nonempty) (hs' : BddAbove s) :
    sSup s = sSup (re '' s) + im hs.choose * I := by
  simp [sSup, hs, hs']

@[simp]
lemma sSup_empty : sSup (∅ : Set ℂ) = 0 := by simp [sSup]

@[simp]
lemma iSup_empty {ι : Type*} [IsEmpty ι] {f : ι → ℂ} : ⨆ i, f i = 0 := by
  simp [← sSup_range, Set.range_eq_empty]

lemma sSup_of_not_bddAbove {s : Set ℂ} (h : ¬BddAbove s) : sSup s = 0 := by simp [sSup, h]

lemma im_eq_im_of_le {x y : ℂ} (h : x ≤ y) : im x = im y := by grind [le_def]

lemma im_const_of_bddAbove' {s : Set ℂ} (hs : BddAbove s) ⦃x : ℂ⦄ (hx : x ∈ s) :
    im x = im hs.choose :=
  im_eq_im_of_le <| hs.choose_spec hx

lemma im_const_of_bddAbove {s : Set ℂ} (hs : BddAbove s) ⦃x y : ℂ⦄ (hx : x ∈ s) (hy : y ∈ s) :
    im x = im y := by
  obtain ⟨b, hb⟩ := hs
  exact hb hx |>.2.trans <| (hb hy).2.symm

lemma im_sSup_of_mem {s : Set ℂ} (hs : BddAbove s) ⦃x : ℂ⦄ (hx : x ∈ s) :
    im (sSup s) = im x := by
  have hs' : s.Nonempty := ⟨x, hx⟩
  simp [sSup_def hs' hs, im_const_of_bddAbove' hs hx,
    im_const_of_bddAbove' hs hs'.choose_spec]

lemma re_sSup {s : Set ℂ} (hs : BddAbove s) : re (sSup s) = sSup (re '' s) := by
  obtain (rfl | h) := s.eq_empty_or_nonempty
  · simp
  · simp [sSup_def h hs]

-- marked high because we want it to fire before `Complex.re_add_im`
@[simp high]
lemma ofReal_add_ofReal_le_iff {x y a b : ℝ} : x + y * I ≤ a + b * I ↔ x ≤ a ∧ y = b := by
  simp [le_def]

lemma monotone_re : Monotone re := by grind [Monotone, le_def]
lemma monotone_im : Monotone im := by grind [Monotone, le_def]

protected lemma le_sSup {s : Set ℂ} (hs : BddAbove s) ⦃x : ℂ⦄ (hx : x ∈ s) :
    x ≤ sSup s := by
  have hs' : s.Nonempty := ⟨x, hx⟩
  rw [← re_add_im x, sSup_def hs' hs, ofReal_add_ofReal_le_iff]
  refine ⟨le_csSup (monotone_re.map_bddAbove hs) (by aesop), ?_⟩
  rw [im_const_of_bddAbove' hs hx, im_const_of_bddAbove' hs hs'.choose_spec]

protected lemma sSup_le {s : Set ℂ} (hs : s.Nonempty) ⦃x : ℂ⦄ (hx : ∀ y ∈ s, y ≤ x) :
    sSup s ≤ x := by
  have bdd : BddAbove s := ⟨x, hx⟩
  rw [← re_add_im x, sSup_def hs bdd, ofReal_add_ofReal_le_iff]
  constructor
  · exact csSup_le (hs.image _) <| by simpa using fun y hy ↦ monotone_re (hx y hy)
  · rw [← im_eq_im_of_le (hx _ hs.choose_spec)]

/-- In `ℂ`, the order is such that any set which is bounded above is directed, which is a
consequence of that fact that any two *comparable* elements have a least upper bound, and
comparabiity is transitive. -/
lemma directedOn_of_bddAbove {s : Set ℂ} (hs : BddAbove s) : DirectedOn (· ≤ ·) s := by
  intro x hx y hy
  have key := im_const_of_bddAbove hs hx hy
  have : max x.re y.re + x.im * I = x ∨ max x.re y.re + x.im * I = y := by
    obtain (h | h) := le_total x.re y.re
    · simp [h, key]
    · simp [h]
  exact ⟨max x.re y.re + x.im * I, by grind, by simp [le_def], by simp [le_def, key]⟩

noncomputable instance : ConditionallyCompletePartialOrderSup ℂ where
  isLUB_csSup_of_directed _ _ h_non h_bdd := ⟨Complex.le_sSup h_bdd, Complex.sSup_le h_non⟩

lemma ofReal_iSup {ι : Type*} {f : ι → ℝ} :
    ofReal (⨆ i, f i) = ⨆ i, ofReal (f i) := by
  obtain (h | h) := isEmpty_or_nonempty ι
  · simp
  by_cases hf : BddAbove (Set.range f)
  · have hf' := by simpa [← Set.range_comp'] using ((monotone_ofReal).map_bddAbove hf)
    rw [← sSup_range, ← sSup_range, ← re_add_im (sSup _), re_sSup hf',
      im_sSup_of_mem hf' ⟨h.some, rfl⟩]
    simp [← Set.range_comp']
  · have : ¬ BddAbove (Set.range (fun i ↦ (f i : ℂ))) :=
      fun h ↦ hf <| by simpa [← Set.range_comp'] using monotone_re.map_bddAbove h
    simp [Real.iSup_of_not_bddAbove hf, ← sSup_range, sSup_of_not_bddAbove this]

lemma IsLUB.image_re {s : Set ℂ} {x : ℂ} (h : IsLUB s x) : IsLUB (re '' s) (re x) := by
  refine ⟨monotone_re.mem_upperBounds_image h.1, fun y hy ↦ ?_⟩
  have := @h.2 (y + x.im * I) fun z hz ↦ by
    rw [← re_add_im z, ofReal_add_ofReal_le_iff]
    exact ⟨hy ⟨z, hz, rfl⟩, (h.1 hz).2⟩
  rw [← re_add_im x, ofReal_add_ofReal_le_iff] at this
  simpa

open Filter Topology Complex
instance : SupConvergenceClass ℂ where
  tendsto_coe_atTop_isLUB z s h := by
    have h₁ : Tendsto (fun x : s ↦ re x) atTop (𝓝 (re z)) := by
      refine tendsto_atTop_isLUB (monotone_re.comp (Subtype.mono_coe s)) ?_
      simpa [← Function.comp_def, Set.range_comp] using h.image_re
    have h₂ : Tendsto (fun x : s ↦ im x) atTop (𝓝 (im z)) := by
      convert tendsto_const_nhds (x := z.im) using 3 with ⟨x, hx⟩
      exact h.1 hx |>.2
    convert (continuous_ofReal.tendsto _ |>.comp h₁).add
      ((continuous_ofReal.tendsto _ |>.comp h₂).const_mul I)
    all_goals simp [mul_comm I]

end Complex
