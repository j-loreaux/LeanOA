import LeanOA.ForMathlib.Topology.Path
import Mathlib.Topology.Connected.PathConnected

variable {G : Type*} [TopologicalSpace G]


@[to_additive]
theorem Joined.mul {x y w z : G} [Mul G] [ContinuousMul G] (hxy : Joined x y) (hwz : Joined w z) :
    Joined (x * w) (y * z) := by
  obtain ⟨γ₁⟩ := hxy
  obtain ⟨γ₂⟩ := hwz
  use γ₁.mul γ₂
  all_goals simp

@[to_additive]
theorem Joined.listProd {l l' : List G} [MulOneClass G] [ContinuousMul G]
    (h : List.Forall₂ Joined l l') :
    Joined l.prod l'.prod := by
  induction h with
  | nil => rfl
  | cons h₁ _ h₂ => exact h₁.mul h₂

@[to_additive]
theorem Joined.inv {x y : G} [Inv G] [ContinuousInv G] (hxy : Joined x y) :
    Joined (x⁻¹) (y⁻¹) := by
  obtain ⟨γ⟩ := hxy
  use γ.inv
  all_goals simp

variable (G)

/-- The path component of the identity in a topological monoid, as a submonoid. -/
@[to_additive (attr := simps)
"The path component of the identity in an additive topological monoid, as an additive submonoid."]
def Submonoid.pathComponentOne [Monoid G] [ContinuousMul G] : Submonoid G where
  carrier := pathComponent (1 : G)
  mul_mem' {g₁ g₂} hg₁ hg₂ := by simpa using hg₁.mul hg₂
  one_mem' := mem_pathComponent_self 1

/-- The path component of the identity in a topological group, as a subgroup. -/
@[to_additive (attr := simps!)
"The path component of the identity in an additive topological group, as an additive subgroup."]
def Subgroup.pathComponentOne [Group G] [IsTopologicalGroup G] : Subgroup G where
  toSubmonoid := .pathComponentOne G
  inv_mem' {g} hg := by simpa using hg.inv

/-- The path component of the identity in a topological group is normal. -/
@[to_additive]
instance Subgroup.Normal.pathComponentOne [Group G] [IsTopologicalGroup G] :
    (Subgroup.pathComponentOne G).Normal where
  conj_mem _ := fun ⟨γ⟩ g ↦ ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩
