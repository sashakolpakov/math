import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentProjectionCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenNormalPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentCycles
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowPullback

/-! # Component Pullback Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentPullbackPreimage.BundleCycles

noncomputable section

/-! The actual graph pullback on each integral component is the restricted Chow preimage from the original full graph construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier) (p : ℕ)

theorem graphComponentPullback_preimage (z : Y.RationalDimensionCycle p) :
    ChowPullback.BundleCycles.graphChowPullback (Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C) p
      (Chow.BundleCycles.cycleToChowQ (Y.componentVariety (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).presentation p
        (PresentationComponentCycles.Bundle.presentationComponentCycle Y (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) p z)) =
      Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass (X.componentVariety C).presentation p
        (Finsupp.comapDomain (X.componentInclusion C)
          (GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage f
            (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))))
          (X.componentInclusion C).isOpenEmbedding.injective.injOn) := by
  let g := Projective.MorphismComponents.BundleCycles.projectiveMorphismOnComponentOver f C
  let a := X.componentInclusionOver C
  let b := Y.componentInclusionOver (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)
  let h := ComponentAmbient.BundleCycles.projectiveMorphismOnComponentOver_square f C
  let β := Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph f).ker (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))
  have hs := OpenCone.BundleCycles.graphCycleSpecialization_open f g a b h (Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))
  have hp := ComponentProjectionCycle.BundleCycles.graphProjectionPointPullback_component f C (Chow.BundleCycles.pointCycle Y p z)
  have hz := PresentationComponentCycles.Bundle.presentationComponentCycle_forget Y (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) p z
  have he : Finsupp.comapDomain (OpenCone.BundleCycles.graphOpenConeMap f g a b h) β
      (OpenCone.BundleCycles.graphOpenConeMap f g a b h).isOpenEmbedding.injective.injOn =
      Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph g).ker
        (Chow.BundleCycles.graphProjectionPointPullback g
          (Chow.BundleCycles.pointCycle (Y.componentVariety (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).presentation p
            (PresentationComponentCycles.Bundle.presentationComponentCycle Y (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) p z))) :=
    hs.trans (congrArg (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (OpenAmbient.BundleCycles.graph g).ker)
      (hp.trans (congrArg (Chow.BundleCycles.graphProjectionPointPullback g) hz.symm)))
  exact (ChowPullback.BundleCycles.graphChowPullback_cycle g p (PresentationComponentCycles.Bundle.presentationComponentCycle Y (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) p z)).trans
    ((congrArg (GraphNormal.InverseChow.BundleCycles.graphNormalInverseChow g p) he.symm).trans
      (OpenNormalPreimage.BundleCycles.graphNormalInverseChow_open_preimage f g a b h p β))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ComponentPullbackPreimage.BundleCycles
