import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleCupEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TripleSumCocycles

/-! # Rectangle Mixed Cup Sum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleMixedCupSum

noncomputable section

/-! Finite sums of mixed projection cups evaluate to the corresponding
alternating tensors in the original native structure-sheaf H1 groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Shuffle

variable {k : Type} [Field k] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {I J : Type} (U : I → X.Opens) (V : J → Y.Opens)

theorem rectangleTripleShuffle_add (v w : RectangleBoundaryShuffle.rectangleOrdinaryCech2 f g U V) :
    RectangleBoundaryShuffle.rectangleTripleShuffle f g U V (fun i j l => v i j l + w i j l) =
      RectangleBoundaryShuffle.rectangleTripleShuffle f g U V v + RectangleBoundaryShuffle.rectangleTripleShuffle f g U V w := by
  funext i i' j j'
  dsimp only [RectangleBoundaryShuffle.rectangleTripleShuffle, Regular.BoundaryShuffle.regularTripleSectionOn, Pi.add_apply]
  rw [map_add, map_add]
  abel

theorem rectangleTripleShuffle_sum {B : Type} (t : Finset B)
    (w : B → RectangleBoundaryShuffle.rectangleOrdinaryCech2 f g U V) :
    RectangleBoundaryShuffle.rectangleTripleShuffle f g U V (fun i j l => ∑ a ∈ t, w a i j l) =
      ∑ a ∈ t, RectangleBoundaryShuffle.rectangleTripleShuffle f g U V (w a) := by
  funext i i' j j'
  simp only [RectangleBoundaryShuffle.rectangleTripleShuffle, Regular.BoundaryShuffle.regularTripleSectionOn, map_sum, Finset.sum_apply]
  exact (Finset.sum_sub_distrib _ _).symm

end Shuffle

local instance mixedCupCohomologyAddGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{0}).obj F))

local instance mixedCupSheafH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf Z.left.sheaf) 1) :=
  StructureComplexScalars.structureH1ComplexModule Z

local instance mixedCupSumH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Z.left) 1) := StructureComplexScalars.structureH1ComplexModule Z

theorem nativeRectangleMixedProjection_mixedCupSum
    (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) {I J B : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype B]
    (U : I → X.left.Opens) (V : J → Y.left.Opens)
    (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (v₁ w₁ : B → ∀ i i', Γ(X.left, U i ⊓ U i'))
    (v₂ w₂ : B → ∀ j j', Γ(Y.left, V j ⊓ V j'))
    (hv₁ : ∀ a, RegularPair.Closed.RegularPairCocycle X.left U (v₁ a))
    (hw₁ : ∀ a, RegularPair.Closed.RegularPairCocycle X.left U (w₁ a))
    (hv₂ : ∀ a, RegularPair.Closed.RegularPairCocycle Y.left V (v₂ a))
    (hw₂ : ∀ a, RegularPair.Closed.RegularPairCocycle Y.left V (w₂ a)) :
    RectangleDetector.nativeRectangleMixedProjection X Y U V hcU hcV hUU hVV
      (RectangleBoundaryShuffle.rectangleTripleShuffle X.hom Y.hom U V (fun i j l => ∑ a,
        (RegularPair.CupSymmetry.regularPairCupTriple (pullback X.hom Y.hom) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V)
          (RectangleCupShuffle.rectangleLeftRegularPair X.hom Y.hom U V (v₁ a))
          (RectangleCupShuffle.rectangleRightRegularPair X.hom Y.hom U V (w₂ a)) i j l +
        RegularPair.CupSymmetry.regularPairCupTriple (pullback X.hom Y.hom) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V)
          (RectangleCupShuffle.rectangleRightRegularPair X.hom Y.hom U V (v₂ a))
          (RectangleCupShuffle.rectangleLeftRegularPair X.hom Y.hom U V (w₁ a)) i j l))) =
      ∑ a, (RegularPair.Closed.regularPairSheafClass X.left U hcU (v₁ a) (hv₁ a) ⊗ₜ[ℂ]
        RegularPair.Closed.regularPairSheafClass Y.left V hcV (w₂ a) (hw₂ a) -
        RegularPair.Closed.regularPairSheafClass X.left U hcU (w₁ a) (hw₁ a) ⊗ₜ[ℂ]
        RegularPair.Closed.regularPairSheafClass Y.left V hcV (v₂ a) (hv₂ a)) := by
  rw [rectangleTripleShuffle_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [rectangleTripleShuffle_add, map_add,
    RectangleCupEvaluation.nativeRectangleMixedProjection_cup_left_right X Y U V hcU hcV hUU hVV
      (v₁ a) (w₂ a) (hv₁ a) (hw₂ a),
    RectangleCupEvaluation.nativeRectangleMixedProjection_cup_right_left X Y U V hcU hcV hUU hVV
      (w₁ a) (v₂ a) (hw₁ a) (hv₂ a), sub_eq_add_neg]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleMixedCupSum
