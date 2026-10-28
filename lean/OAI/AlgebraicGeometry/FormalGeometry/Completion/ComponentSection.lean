import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FiberComponents

/-! # Component Section -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ComponentSection.Construction

noncomputable section

/-!
# Completion: an actual section factors through its connected component
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} [IsNoetherian X] [PreconnectedSpace Y]
  (s : Y ⟶ X) (y : Y)

/-- The image of a connected source lies in the component of any of its image points. -/
theorem schemeMap_component_range :
    Set.range s ⊆ Set.range (Proper.FiberComponents.Construction.noetherianComponentOpen X (s y)).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  exact s.continuous.mapsTo_connectedComponent y (by simp)

/-- The actual factorization of a scheme map through its open connected component. -/
def schemeMapToComponent : Y ⟶ (Proper.FiberComponents.Construction.noetherianComponentOpen X (s y)).toScheme :=
  IsOpenImmersion.lift _ s (schemeMap_component_range s y)

@[reassoc]
theorem schemeMapToComponent_ι :
    schemeMapToComponent s y ≫ (Proper.FiberComponents.Construction.noetherianComponentOpen X (s y)).ι = s :=
  IsOpenImmersion.lift_fac _ _ _

/-- A section remains a section after factoring through its actual connected component. -/
theorem schemeMapToComponent_section (f : X ⟶ Y) (hs : s ≫ f = 𝟙 Y) :
    schemeMapToComponent s y ≫ ((Proper.FiberComponents.Construction.noetherianComponentOpen X (s y)).ι ≫ f) = 𝟙 Y := by
  rw [← Category.assoc, schemeMapToComponent_ι, hs]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ComponentSection.Construction
