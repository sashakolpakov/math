import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PullbackCech
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechRefinedPullback

/-! # Class Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassPullback

noncomputable section

/-! Native H1 pullback carries the class of a regular pair cocycle
to the class of its original pair-section pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) {I : Type} (U : I → B.left.Opens)
    (hU : iSup U = ⊤) (v : ∀ i j : I, Γ(B.left, U i ⊓ U j))
    (hv : Closed.RegularPairCocycle B.left U v)

theorem regularPairSheafClass_pullback :
    StructurePullback.nativeStructureH1Pullback f
        (show SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule B.left) 1 from Closed.regularPairSheafClass B.left U hU v hv) =
      (show SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.left) 1 from
        Closed.regularPairSheafClass A.left (fun i => f.left ⁻¹ᵁ U i) (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU)
          (PairPullback.regularPairPullback f.left U v) (PairPullback.regularPairPullback_cocycle f.left U v hv)) := by
  have h := StructureCechRefinedPullback.nativeStructureH1Pullback_cechClass f U hU (Closed.regularPairCechCochain B.left U v)
    (Closed.regularPairCechCochain_closed B.left U v hv)
  have hc := PullbackCech.regularPairPullback_cech f.left U v
  refine h.trans ?_
  unfold StructureCechPullbackData.nativeStructureCechClass Closed.regularPairSheafClass
  congr 1

theorem regularPairSheafClass_pullbackLinear :
    StructurePullbackLinear.nativeStructureH1PullbackLinear f
        (show SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule B.left) 1 from Closed.regularPairSheafClass B.left U hU v hv) =
      (show SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.left) 1 from
        Closed.regularPairSheafClass A.left (fun i => f.left ⁻¹ᵁ U i) (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU)
          (PairPullback.regularPairPullback f.left U v) (PairPullback.regularPairPullback_cocycle f.left U v hv)) :=
  regularPairSheafClass_pullback f U hU v hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassPullback
