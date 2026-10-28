import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentAmbient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponentPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProductClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen

/-! # Component Projection Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentProjectionLift.BundleCycles

noncomputable section

section

/-! The graph product of the actual source and receiving target components maps openly into the source-component product with the full target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

theorem graphProjectionComponentInclusion_range :
    Set.range (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C) =
      OpenAmbient.BundleCycles.graphFirstProjection f ⁻¹' Set.range (X.componentInclusion C) := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback (f.left ≫ Y.structureMap)
      (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) (X.componentInclusion C) rfl Y.structureMap).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h

theorem graphComponentAmbientMap_range_subset :
    Set.range (ComponentAmbient.BundleCycles.graphComponentAmbientMap f C) ⊆ Set.range (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C) := by
  rintro _ ⟨x, rfl⟩
  rw [graphProjectionComponentInclusion_range]
  change OpenAmbient.BundleCycles.graphFirstProjection f (ComponentAmbient.BundleCycles.graphComponentAmbientMap f C x) ∈ Set.range (X.componentInclusion C)
  exact ⟨OpenAmbient.BundleCycles.graphFirstProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) x,
    (congrArg (fun k => k x) (ComponentAmbient.BundleCycles.graphComponentAmbientMap_first f C)).symm⟩

def graphComponentProjectionLift : OpenAmbient.BundleCycles.graphAmbient (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) ⟶ ProjectionComponents.BundleCycles.graphProjectionComponent f C :=
  IsOpenImmersion.lift (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C) (ComponentAmbient.BundleCycles.graphComponentAmbientMap f C)
    (graphComponentAmbientMap_range_subset f C)

theorem graphComponentProjectionLift_inclusion :
    graphComponentProjectionLift f C ≫ ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C = ComponentAmbient.BundleCycles.graphComponentAmbientMap f C :=
  IsOpenImmersion.lift_fac _ _ _

instance graphComponentProjectionLift_open : IsOpenImmersion (graphComponentProjectionLift f C) := by
  have h : IsOpenImmersion (graphComponentProjectionLift f C ≫ ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C) :=
    (congrArg (fun k => IsOpenImmersion k) (graphComponentProjectionLift_inclusion f C)).mpr
      (ComponentAmbient.BundleCycles.graphComponentAmbientMap_open f C)
  exact IsOpenImmersion.of_comp (graphComponentProjectionLift f C) (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C)

theorem graphComponentProjectionLift_projection :
    graphComponentProjectionLift f C ≫ ProjectionComponents.BundleCycles.graphProjectionComponentMap f C =
      OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) ≫
        Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) := by
  exact (congrArg (fun k => graphComponentProjectionLift f C ≫ k) (ProjectionComponents.BundleCycles.graphProjectionComponent_over f C)).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ OpenAmbient.BundleCycles.graphSecondProjection f) (graphComponentProjectionLift_inclusion f C)).trans
        (ComponentAmbient.BundleCycles.graphComponentAmbientMap_second f C)))

theorem graphComponentAmbientMap_fiberGenericPoint (y : (Y.componentVariety (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).carrier) :
    ComponentAmbient.BundleCycles.graphComponentAmbientMap f C (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)) y) =
      ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f C (Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) y) := by
  have h := Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare (ProjectionComponents.BundleCycles.graphProjectionComponentMap f C)
    (OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C))
    (Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)) (graphComponentProjectionLift f C)
    (graphComponentProjectionLift_projection f C).symm y
  exact (congrArg (fun k => k (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)) y))
    (graphComponentProjectionLift_inclusion f C)).symm.trans
    (congrArg (ProjectionComponents.BundleCycles.graphProjectionComponentInclusion f C) h)

end

/-! A projection-fiber component meets the restricted graph product precisely on the selected source component and the actual receiving target component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

theorem graphComponentAmbientMap_componentPoint_mem_iff (B : irreducibleComponents X.carrier) (y : Y.carrier) :
    ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f B y ∈ Set.range (ComponentAmbient.BundleCycles.graphComponentAmbientMap f C) ↔
      B = C ∧ y ∈ Set.range (Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)) := by
  constructor
  · rintro ⟨t, ht⟩
    have hC : OpenAmbient.BundleCycles.graphFirstProjection f (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f B y) ∈ Set.range (X.componentInclusion C) := by
      refine ⟨OpenAmbient.BundleCycles.graphFirstProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) t, ?_⟩
      exact (congrArg (fun k => k t) (ComponentAmbient.BundleCycles.graphComponentAmbientMap_first f C)).symm.trans
        (congrArg (OpenAmbient.BundleCycles.graphFirstProjection f) ht)
    have hB := ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint_first_mem f B y
    obtain ⟨D, _, hD⟩ := ProjectionComponents.BundleCycles.projectiveComponents_cover X (OpenAmbient.BundleCycles.graphFirstProjection f (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint f B y))
    refine ⟨(hD B hB).trans (hD C hC).symm, ?_⟩
    refine ⟨OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) t, ?_⟩
    exact (congrArg (fun k => k t) (ComponentAmbient.BundleCycles.graphComponentAmbientMap_second f C)).symm.trans
      ((congrArg (OpenAmbient.BundleCycles.graphSecondProjection f) ht).trans (ProjectionComponentPoint.BundleCycles.graphProjectionComponentPoint_second f B y))
  · rintro ⟨hBC, z, rfl⟩
    subst B
    exact ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)) z,
      graphComponentAmbientMap_fiberGenericPoint f C z⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentProjectionLift.BundleCycles
