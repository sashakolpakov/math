import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MorphismComponents
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRelativeDimension
import OAI.AlgebraicGeometry.Betti.SmoothDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension

/-! # Target Component -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.TargetComponent.BundleCycles

noncomputable section

/-! The part of the graph ambient product over a target component has
the component's actual smooth relative dimension over the source. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem projectiveComponent_smoothRelativeDimension (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (D : irreducibleComponents Y.carrier) :
    SmoothOfRelativeDimension (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety D).structureMap)
      (Y.componentVariety D).structureMap := by
  let : Smooth (Y.componentVariety D).structureMap := by
    rw [← Y.componentInclusion_over D]
    let : IsOpenImmersion (Y.componentInclusion D) := Y.componentInclusion_isOpenImmersion D
    infer_instance
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  exact Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension (Y.componentVariety D).structureMap

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphTargetComponent (D : irreducibleComponents Y.carrier) : Scheme :=
  pullback (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D)

def graphTargetComponentInclusion (D : irreducibleComponents Y.carrier) :
    graphTargetComponent f D ⟶ OpenAmbient.BundleCycles.graphAmbient f := pullback.fst (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D)

def graphTargetComponentFirst (D : irreducibleComponents Y.carrier) :
    graphTargetComponent f D ⟶ X.carrier := graphTargetComponentInclusion f D ≫ OpenAmbient.BundleCycles.graphFirstProjection f

instance graphTargetComponentInclusion_isOpenImmersion (D : irreducibleComponents Y.carrier) :
    IsOpenImmersion (graphTargetComponentInclusion f D) := by
  let : IsOpenImmersion (Y.componentInclusion D) := Y.componentInclusion_isOpenImmersion D
  exact inferInstanceAs (IsOpenImmersion (pullback.fst (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D)))

instance graphTargetComponentInclusion_isClosedImmersion (D : irreducibleComponents Y.carrier) :
    IsClosedImmersion (graphTargetComponentInclusion f D) := by
  let : IsClosedImmersion (Y.componentInclusion D) := Y.componentInclusion_isClosedImmersion D
  exact inferInstanceAs (IsClosedImmersion (pullback.fst (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D)))

theorem graphTargetComponent_isPullback (D : irreducibleComponents Y.carrier) :
    IsPullback (pullback.snd (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D))
      (graphTargetComponentFirst f D) (Y.componentVariety D).structureMap
      (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap) := by
  have hg : IsPullback (OpenAmbient.BundleCycles.graphSecondProjection f) (OpenAmbient.BundleCycles.graphFirstProjection f) Y.structureMap
      (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap) :=
    (IsPullback.of_hasPullback (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap) Y.structureMap).flip
  have H := (IsPullback.of_hasPullback (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D)).flip.paste_vert hg
  rw [Y.componentInclusion_over] at H
  exact H

theorem graphTargetComponentFirst_relativeDimension (D : irreducibleComponents Y.carrier) :
    SmoothOfRelativeDimension (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety D).structureMap)
      (graphTargetComponentFirst f D) := by
  let n := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety D).structureMap
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback (graphTargetComponent_isPullback f D)
    (projectiveComponent_smoothRelativeDimension Y D)

theorem graphTargetComponentInclusion_range (D : irreducibleComponents Y.carrier) :
    Set.range (graphTargetComponentInclusion f D) = OpenAmbient.BundleCycles.graphSecondProjection f ⁻¹' Set.range (Y.componentInclusion D) :=
  PullbackRange.BundleCycles.range_of_isPullback (IsPullback.of_hasPullback (OpenAmbient.BundleCycles.graphSecondProjection f) (Y.componentInclusion D))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.TargetComponent.BundleCycles
