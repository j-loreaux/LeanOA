module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded

public section

open Set Topology WeakDual Metric

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [AddCommGroup F] [Module 𝕜 F]

def seminorm_point_on_F (v : V) (b : F →ₗ[𝕜] V →ₗ[𝕜] 𝕜) : Seminorm 𝕜 F :=
    Seminorm.comp (normSeminorm 𝕜 𝕜) (b.flip v)

def seminorm_point_on_V (f : F) (b : F →ₗ[𝕜] V →ₗ[𝕜] 𝕜) : Seminorm 𝕜 V :=
    Seminorm.comp (normSeminorm 𝕜 𝕜) (b f)

/- I think this is already in Mathlib as `polar` associated to `b`. -/
def nhd_polar (U : Set V) (b : F →ₗ[𝕜] V →ₗ[𝕜] 𝕜) : Set F :=
  {f | ∀ v ∈ U, (seminorm_point_on_F v b) f ≤ 1}

variable [TopologicalSpace V] [ContinuousSMul 𝕜 V]

variable (U : Set V) (b : F →ₗ[𝕜] V →ₗ[𝕜] 𝕜) (U_nhds : U ∈ 𝓝 (0 : V))

def s := {p | ∃ f ∈ nhd_polar U b, p = seminorm_point_on_V f b}

lemma absorbing (v : V) : ∃ t : 𝕜, t ≠ 0 ∧ t • v ∈ U := by sorry

/- This should be generalized, and furthermore ought to already exist! -/
lemma pointwise_bound (v : V) : ∃ M, ∀ p ∈ s U b, p v ≤ M := by
  obtain ⟨t , htnz, ht⟩ := absorbing (𝕜 := 𝕜) U v
  use ‖t‖⁻¹
  have h : 0 < ‖t‖ := by aesop
  intro p hp
  obtain ⟨f, hfmem, hdef⟩ := hp
  rw [hdef]
  dsimp [seminorm_point_on_V]
  have A := LinearMap.polar_mem b (fun x ↦ ‖(b x) (t • v)‖ ≤ 1)
     (t • v) (fun x a ↦ a) f (hfmem (t • v) ht)
  grw [LinearMap.map_smul (b f) t v, norm_smul t ((b f) v)] at A
  have F : ‖t‖ * ‖t‖⁻¹ = 1 := by aesop
  have D : ‖t‖ * ‖(b f) v‖ ≤ ‖t‖ * ‖t‖⁻¹ := le_of_le_of_eq A (id (Eq.symm F))
  exact (mul_le_mul_iff_of_pos_left h).mp D

theorem correct_bddness : BddAbove ((↑)'' (s U b) : Set (V → ℝ)) := by
  choose g hg using pointwise_bound U b
  refine ⟨g, ?_⟩
  intro f hf
  rcases hf with ⟨p, hp, rfl⟩
  intro v
  exact hg v p hp

/- It seems that `Seminorm 𝕜 F` is a SupSet, i.e. one can define
   `sSup s` for any `s : Set (Seminorm 𝕜 F)`. The `SupSet` instance
   gives a conditional, though, and so if there isn't a proof that the
   family of seminorms is pointwise bounded as functions, then `sSup s = ⊥`.
   So it seems the way to work with this is to supply `correct_bddness` above
   as an argument to `Seminorm.sSup_apply` to ensure that the right formula is used
   for the Mackey-Arens Seminorm. -/

end
