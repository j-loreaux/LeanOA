import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import LeanOA.Mathlib.Topology.ContinuousMap.Compact

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

open scoped CStarAlgebra in
open Unitization in
lemma CommCStarAlgebra.norm_add_eq_max {a b : A} (h : a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalAlgHom ℂ A
  have hf : Isometry f := gelfandTransform_isometry _ |>.comp isometry_inr
  simp_rw [← hf.norm_map_of_map_zero (by simp [f]), show f (a + b) = f a + f b by simp [f]]
  exact ContinuousMap.norm_add_eq_max <| by simpa [f] using congr(f $h)

open NonUnitalStarAlgebra in
lemma IsSelfAdjoint.norm_add_eq_max {A : Type*} [NonUnitalCStarAlgebra A]
    {a b : A} (hab : a * b = 0) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let S : NonUnitalStarSubalgebra ℂ A := (adjoin ℂ {a, b}).topologicalClosure
  have hS : IsClosed (S : Set A) := (adjoin ℂ {a, b}).isClosed_topologicalClosure
  have hab' : a * b = b * a := by
    rw [hab, eq_comm]; simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  let _ : NonUnitalCommRing (adjoin ℂ {a, b}) :=
    adjoinNonUnitalCommRingOfComm ℂ (by grind) (by grind [IsSelfAdjoint.star_eq])
  let _ : NonUnitalCommRing S := (adjoin ℂ {a, b}).nonUnitalCommRingTopologicalClosure mul_comm
  let _ : NonUnitalCommCStarAlgebra S := { }
  let c : S := ⟨a, subset_closure <| subset_adjoin _ _ <| by grind⟩
  let d : S := ⟨b, subset_closure <| subset_adjoin _ _ <| by grind⟩
  exact CommCStarAlgebra.norm_add_eq_max (a := c) (b := d) (by ext; simpa)

lemma IsSelfAdjoint.norm_sub_eq_max {A : Type*} [NonUnitalCStarAlgebra A]
    {a b : A} (hab : a * b = 0) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    ‖a - b‖ = max ‖a‖ ‖b‖ := by
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp only [sq, ← ha.norm_add_eq_max hab hb, ← CStarRing.norm_star_mul_self]
  have : b * a = 0 := by simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  simp [sub_mul, mul_sub, hb.star_eq, ha.star_eq, hab, this, add_mul, mul_add]
