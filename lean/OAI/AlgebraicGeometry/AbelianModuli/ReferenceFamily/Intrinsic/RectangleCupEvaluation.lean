import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleCupShuffle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleDetector

/-! # Rectangle Cup Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleCupEvaluation

noncomputable section

/-! The mixed rectangle detector evaluates actual projection cups
in the tensor of the two original structure-sheaf H1 groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance rectangleCupCohomologyAddGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{0}).obj F))

local instance rectangleCupSheafH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf Z.left.sheaf) 1) :=
  StructureComplexScalars.structureH1ComplexModule Z

local instance rectangleCupH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Z.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule Z

def nativeRegularPairCycle (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {I : Type} (U : I → X.left.Opens)
    (v : ∀ i i', Γ(X.left, U i ⊓ U i')) (hv : RegularPair.Closed.RegularPairCocycle X.left U v) :
    LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) :=
  ⟨v, (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_eq_zero_iff (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U v).mpr
    (fun i i' i'' W hi hi' hi'' => Regular.CupClosedSections.regularPairCocycle_on X.left U v hv i i' i'' W hi hi' hi'')⟩

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : I → X.left.Opens) (V : J → Y.left.Opens)
    (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (v : ∀ i i', Γ(X.left, U i ⊓ U i')) (w : ∀ j j', Γ(Y.left, V j ⊓ V j'))
    (hv : RegularPair.Closed.RegularPairCocycle X.left U v) (hw : RegularPair.Closed.RegularPairCocycle Y.left V w)

theorem nativeRectangleMixedProjection_cup_left_right :
    RectangleDetector.nativeRectangleMixedProjection X Y U V hcU hcV hUU hVV
      (RectangleBoundaryShuffle.rectangleTripleShuffle X.hom Y.hom U V
        (RegularPair.CupSymmetry.regularPairCupTriple (pullback X.hom Y.hom) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V)
          (RectangleCupShuffle.rectangleLeftRegularPair X.hom Y.hom U V v)
          (RectangleCupShuffle.rectangleRightRegularPair X.hom Y.hom U V w))) =
      RegularPair.Closed.regularPairSheafClass X.left U hcU v hv ⊗ₜ[ℂ]
        RegularPair.Closed.regularPairSheafClass Y.left V hcV w hw := by
  rw [RectangleCupShuffle.rectangleTripleShuffle_cup_left_right X.hom Y.hom U V hUU hVV v w hv]
  have result := RectangleDetector.nativeRectangleMixedProjection_cycles X Y U V hcU hcV hUU hVV
    (nativeRegularPairCycle X U v hv) (nativeRegularPairCycle Y V w hw)
  convert result using 2 <;> rfl

theorem nativeRectangleMixedProjection_cup_right_left :
    RectangleDetector.nativeRectangleMixedProjection X Y U V hcU hcV hUU hVV
      (RectangleBoundaryShuffle.rectangleTripleShuffle X.hom Y.hom U V
        (RegularPair.CupSymmetry.regularPairCupTriple (pullback X.hom Y.hom) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V)
          (RectangleCupShuffle.rectangleRightRegularPair X.hom Y.hom U V w)
          (RectangleCupShuffle.rectangleLeftRegularPair X.hom Y.hom U V v))) =
      -(RegularPair.Closed.regularPairSheafClass X.left U hcU v hv ⊗ₜ[ℂ]
        RegularPair.Closed.regularPairSheafClass Y.left V hcV w hw) := by
  rw [RectangleCupShuffle.rectangleTripleShuffle_cup_right_left X.hom Y.hom U V hUU hVV v w hw, map_neg]
  apply congrArg Neg.neg
  convert (RectangleDetector.nativeRectangleMixedProjection_cycles X Y U V hcU hcV hUU hVV
    (nativeRegularPairCycle X U v hv) (nativeRegularPairCycle Y V w hw)) using 2 <;> rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleCupEvaluation
