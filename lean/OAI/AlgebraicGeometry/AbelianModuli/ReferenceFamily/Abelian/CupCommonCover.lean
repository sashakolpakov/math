import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.RefinementOperations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.RefinedPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleCupShuffle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleClassDetection

/-! # Cup Common Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CupCommonCover

noncomputable section

/-! Intersect the rectangle cover with the inverse-image cover for
multiplication. This actual open cover refines all three map covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [MonObj X] {I : Type} (U : I → X.left.Opens)

def abelianCupCommonCover (p : (Σ _ : I, I) × I) : (X ⊗ X).left.Opens :=
  Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U p.1 ⊓
    (fst X X * snd X X).left ⁻¹ᵁ U p.2

theorem abelianCupCommonCover_covers (hU : iSup U = ⊤) :
    iSup (abelianCupCommonCover X U) = ⊤ :=
  Regular.RefinementOperations.commonOpenCover_covers (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U)
    (fun i => (fst X X * snd X X).left ⁻¹ᵁ U i)
    (RectangleClassDetection.rectangleOpenCover_covers X.hom X.hom U U hU hU)
    (Inverse.ImageCechCover.inverseImageCechCover_covers (fst X X * snd X X).left.base U hU)

theorem abelianCupCommonCover_leftPair
    (v : ∀ i j, Γ(X.left, U i ⊓ U j)) :
    RegularPair.Refinement.regularPairRefinement (X ⊗ X).left (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U)
      (abelianCupCommonCover X U) Prod.fst (fun _ => inf_le_left)
      (RectangleCupShuffle.rectangleLeftRegularPair X.hom X.hom U U v) =
      RegularPair.RefinedPullback.regularPairRefinedPullback (fst X X) U (abelianCupCommonCover X U)
        (fun p => p.1.1) (fun _ => inf_le_left.trans inf_le_left) v := by
  exact Regular.RefinementOperations.regularPairRefinement_comp (X ⊗ X).left (fun i => (fst X X).left ⁻¹ᵁ U i)
    (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U) (abelianCupCommonCover X U)
    Sigma.fst Prod.fst (fun _ => inf_le_left) (fun _ => inf_le_left)
    (RegularPair.PairPullback.regularPairPullback (fst X X).left U v)

theorem abelianCupCommonCover_rightPair
    (v : ∀ i j, Γ(X.left, U i ⊓ U j)) :
    RegularPair.Refinement.regularPairRefinement (X ⊗ X).left (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U)
      (abelianCupCommonCover X U) Prod.fst (fun _ => inf_le_left)
      (RectangleCupShuffle.rectangleRightRegularPair X.hom X.hom U U v) =
      RegularPair.RefinedPullback.regularPairRefinedPullback (snd X X) U (abelianCupCommonCover X U)
        (fun p => p.1.2) (fun _ => inf_le_left.trans inf_le_right) v := by
  exact Regular.RefinementOperations.regularPairRefinement_comp (X ⊗ X).left (fun i => (snd X X).left ⁻¹ᵁ U i)
    (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom X.hom U U) (abelianCupCommonCover X U)
    (fun p => p.2) Prod.fst (fun _ => inf_le_right) (fun _ => inf_le_left)
    (RegularPair.PairPullback.regularPairPullback (snd X X).left U v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CupCommonCover
