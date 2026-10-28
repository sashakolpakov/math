import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MorphismComponents
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent

/-! # Component Ambient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentAmbient.BundleCycles

noncomputable section

/-! Each source component and its actual receiving target component determine an open cartesian restriction of the original graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

theorem projectiveMorphismOnComponentOver_square :
    X.componentInclusionOver C ≫ f =
      Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C ≫ Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) := by
  apply Over.OverMorphism.ext
  exact (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponent_inclusion f C).symm

def graphComponentAmbientMap : OpenAmbient.BundleCycles.graphAmbient (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) ⟶ OpenAmbient.BundleCycles.graphAmbient f :=
  OpenAmbient.BundleCycles.graphOpenAmbientMap f (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
    (X.componentInclusionOver C) (Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C))

instance graphComponentAmbientMap_open : IsOpenImmersion (graphComponentAmbientMap f C) :=
  OpenAmbient.BundleCycles.graphOpenAmbientMap_open f (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
    (X.componentInclusionOver C) (Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C))

theorem graphComponentAmbientMap_first :
    graphComponentAmbientMap f C ≫ OpenAmbient.BundleCycles.graphFirstProjection f =
      OpenAmbient.BundleCycles.graphFirstProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) ≫ X.componentInclusion C :=
  OpenAmbient.BundleCycles.graphOpenAmbientMap_first f (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
    (X.componentInclusionOver C) (Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C))

theorem graphComponentAmbientMap_second :
    graphComponentAmbientMap f C ≫ OpenAmbient.BundleCycles.graphSecondProjection f =
      OpenAmbient.BundleCycles.graphSecondProjection (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) ≫
        Y.componentInclusion (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) :=
  OpenAmbient.BundleCycles.graphOpenAmbientMap_second f (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
    (X.componentInclusionOver C) (Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C))

theorem graphComponentAmbientMap_isPullback :
    IsPullback (OpenAmbient.BundleCycles.graph (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)) (X.componentInclusion C)
      (graphComponentAmbientMap f C) (OpenAmbient.BundleCycles.graph f) :=
  OpenSquare.BundleCycles.graphOpenAmbientMap_isPullback f (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
    (X.componentInclusionOver C) (Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C))
    (projectiveMorphismOnComponentOver_square f C)

theorem graphComponentAmbientMap_kernel :
    (OpenAmbient.BundleCycles.graph f).ker.comap (graphComponentAmbientMap f C) = (OpenAmbient.BundleCycles.graph (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)).ker :=
  OpenSquare.BundleCycles.graphOpenAmbientMap_kernel f (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C)
    (X.componentInclusionOver C) (Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C))
    (projectiveMorphismOnComponentOver_square f C)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentAmbient.BundleCycles
