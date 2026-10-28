import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents
import Mathlib.Topology.Connected.Clopen

/-! # Morphism Components -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MorphismComponents.BundleCycles

noncomputable section

/-! An arbitrary morphism sends each actual integral source component
into a unique actual target component. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def projectiveComponentMapToTarget (C : irreducibleComponents X.carrier) :
    (X.componentVariety C).carrier ⟶ Y.carrier :=
  X.componentInclusion C ≫ (show X.carrier ⟶ Y.carrier from f.left)

def projectiveMorphismComponent (C : irreducibleComponents X.carrier) : irreducibleComponents Y.carrier :=
  Classical.choose (Graph.ProjectionComponents.BundleCycles.projectiveComponents_cover Y
    (projectiveComponentMapToTarget f C (genericPoint (X.componentVariety C).carrier)))

theorem projectiveMorphismComponent_generic_mem (C : irreducibleComponents X.carrier) :
    projectiveComponentMapToTarget f C (genericPoint (X.componentVariety C).carrier) ∈
      Set.range (Y.componentInclusion (projectiveMorphismComponent f C)) :=
  (Classical.choose_spec (Graph.ProjectionComponents.BundleCycles.projectiveComponents_cover Y
    (projectiveComponentMapToTarget f C (genericPoint (X.componentVariety C).carrier)))).1

theorem projectiveMorphismComponent_range (C : irreducibleComponents X.carrier) :
    Set.range (projectiveComponentMapToTarget f C) ⊆
      Set.range (Y.componentInclusion (projectiveMorphismComponent f C)) := by
  let D := projectiveMorphismComponent f C
  let : IsOpenImmersion (Y.componentInclusion D) := Y.componentInclusion_isOpenImmersion D
  let : IsClosedImmersion (Y.componentInclusion D) := Y.componentInclusion_isClosedImmersion D
  have hi : IsIrreducible (Set.range (projectiveComponentMapToTarget f C)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X.componentVariety C).carrier).image
        (projectiveComponentMapToTarget f C) (projectiveComponentMapToTarget f C).continuous.continuousOn
  exact hi.isConnected.isPreconnected.subset_isClopen
    ⟨(Y.componentInclusion D).isClosedEmbedding.isClosed_range, (Y.componentInclusion D).isOpenEmbedding.isOpen_range⟩
    ⟨_, ⟨genericPoint (X.componentVariety C).carrier, rfl⟩, projectiveMorphismComponent_generic_mem f C⟩

def projectiveMorphismOnComponent (C : irreducibleComponents X.carrier) :
    (X.componentVariety C).carrier ⟶ (Y.componentVariety (projectiveMorphismComponent f C)).carrier := by
  let : IsOpenImmersion (Y.componentInclusion (projectiveMorphismComponent f C)) :=
    Y.componentInclusion_isOpenImmersion _
  exact IsOpenImmersion.lift (Y.componentInclusion (projectiveMorphismComponent f C))
    (projectiveComponentMapToTarget f C) (projectiveMorphismComponent_range f C)

theorem projectiveMorphismOnComponent_inclusion (C : irreducibleComponents X.carrier) :
    projectiveMorphismOnComponent f C ≫ Y.componentInclusion (projectiveMorphismComponent f C) =
      projectiveComponentMapToTarget f C := by
  let : IsOpenImmersion (Y.componentInclusion (projectiveMorphismComponent f C)) :=
    Y.componentInclusion_isOpenImmersion _
  exact IsOpenImmersion.lift_fac _ _ _

theorem projectiveMorphismOnComponent_over (C : irreducibleComponents X.carrier) :
    projectiveMorphismOnComponent f C ≫ (Y.componentVariety (projectiveMorphismComponent f C)).structureMap =
      (X.componentVariety C).structureMap := by
  have hf : (show X.carrier ⟶ Y.carrier from f.left) ≫ Y.structureMap = X.structureMap := f.w
  rw [← Y.componentInclusion_over, ← Category.assoc, projectiveMorphismOnComponent_inclusion]
  change (X.componentInclusion C ≫ (show X.carrier ⟶ Y.carrier from f.left)) ≫ Y.structureMap = _
  rw [Category.assoc, hf, X.componentInclusion_over]

def projectiveMorphismOnComponentOver (C : irreducibleComponents X.carrier) :
    (X.componentVariety C).toOver ⟶ (Y.componentVariety (projectiveMorphismComponent f C)).toOver :=
  Over.homMk (projectiveMorphismOnComponent f C) (projectiveMorphismOnComponent_over f C)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MorphismComponents.BundleCycles
