import Mathlib.Algebra.Order.Star.Basic

lemma IsSelfAdjoint.iff_of_le {R : Type*} [NonUnitalRing R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] {a b : R} (hab : a ≤ b) :
    IsSelfAdjoint a ↔ IsSelfAdjoint b := by
  replace hab := (sub_nonneg.mpr hab).isSelfAdjoint
  exact ⟨fun ha ↦ by simpa using hab.add ha, fun hb ↦ by simpa using (hab.sub hb).neg⟩

alias ⟨IsSelfAdjoint.of_ge, IsSelfAdjoint.of_le⟩ := IsSelfAdjoint.iff_of_le
