import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Components

/-! # Component Morphisms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ComponentMorphisms.Components

noncomputable section

/-! Restrict an actual scheme morphism to its source and target integral components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem exists_component_target (C : irreducibleComponents X.left) :
    ∃ D : irreducibleComponents Y.left, f.left '' C.val ⊆ D.val := by
  obtain ⟨D, hD, h⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (f.left '' C.val) (C.property.1.image f.left f.left.continuous.continuousOn)
  exact ⟨⟨D, hD⟩, h⟩

def componentTarget (C : irreducibleComponents X.left) : irreducibleComponents Y.left :=
  (exists_component_target f C).choose

theorem componentTarget_contains (C : irreducibleComponents X.left) :
    f.left '' C.val ⊆ (componentTarget f C).val :=
  (exists_component_target f C).choose_spec

variable [Smooth X.hom] [QuasiCompact X.hom] [Smooth Y.hom] [QuasiCompact Y.hom]

theorem componentMap_range (C : irreducibleComponents X.left) :
    Set.range (Betti.Smooth.Components.componentInclusion X C ≫ f).left ⊆
      Set.range (Betti.Smooth.Components.componentInclusion Y (componentTarget f C)).left := by
  rw [Betti.Smooth.Components.componentInclusion_range]
  rintro _ ⟨x, rfl⟩
  apply componentTarget_contains f C
  refine ⟨(Betti.Smooth.Components.componentInclusion X C).left x, ?_, rfl⟩
  rw [← Betti.Smooth.Components.componentInclusion_range]
  exact ⟨x, rfl⟩

def componentMap (C : irreducibleComponents X.left) :
    Betti.Smooth.Components.componentOver X C ⟶ Betti.Smooth.Components.componentOver Y (componentTarget f C) :=
  Over.homMk (IsOpenImmersion.lift (Betti.Smooth.Components.componentInclusion Y (componentTarget f C)).left
    (Betti.Smooth.Components.componentInclusion X C ≫ f).left (componentMap_range f C)) (by
      change IsOpenImmersion.lift _ _ _ ≫
        ((Betti.Smooth.Components.componentInclusion Y (componentTarget f C)).left ≫ Y.hom) = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w (Betti.Smooth.Components.componentInclusion X C ≫ f))

theorem componentMap_fac (C : irreducibleComponents X.left) :
    componentMap f C ≫ Betti.Smooth.Components.componentInclusion Y (componentTarget f C) = Betti.Smooth.Components.componentInclusion X C ≫ f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ (componentMap_range f C)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ComponentMorphisms.Components
