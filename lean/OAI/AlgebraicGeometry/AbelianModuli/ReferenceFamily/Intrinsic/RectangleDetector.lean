import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.CycleIntrinsicClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleClassDetection

/-! # Rectangle Detector -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleDetector

noncomputable section

/-! The mixed rectangle detector takes values in the tensor of the
original structure-sheaf H1 groups. It evaluates actual cycle products
as their native H1 tensors and annihilates zero native H2 classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance nativeRectangleCohomologyAddGroup {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{0}).obj F))

local instance nativeRectangleH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Z.left) 1) := StructureComplexScalars.structureH1ComplexModule Z

local instance nativeRectangleSheafH1Module (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf Z.left.sheaf) 1) :=
  StructureComplexScalars.structureH1ComplexModule Z

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : I → X.left.Opens) (V : J → Y.left.Opens)
    (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i')) (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

def nativeRectangleMixedProjection : Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCech11 X.hom Y.hom U V →ₗ[ℂ]
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 ⊗[ℂ] SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Y.left) 1 :=
  (TensorProduct.map (Open.CycleIntrinsicClass.nativeOpenCechCycleQuotientClass X U hcU)
    (Open.CycleIntrinsicClass.nativeOpenCechCycleQuotientClass Y V hcV)).comp
      (RectangleMixedClassProjection.rectangleMixedClassProjection X.hom Y.hom U V hUU hVV)

theorem nativeRectangleMixedProjection_cycles
    (x : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U))
    (y : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf Y.hom) V)) :
    nativeRectangleMixedProjection X Y U V hcU hcV hUU hVV
      (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv X.hom Y.hom U V hUU hVV (x.val ⊗ₜ[ℂ] y.val)) =
      RegularPair.Closed.regularPairSheafClass X.left U hcU x.val (Open.CycleIntrinsicClass.openModuleCycle_regular X U x) ⊗ₜ[ℂ]
        RegularPair.Closed.regularPairSheafClass Y.left V hcV y.val (Open.CycleIntrinsicClass.openModuleCycle_regular Y V y) := by
  change TensorProduct.map _ _ (RectangleMixedClassProjection.rectangleMixedClassProjection X.hom Y.hom U V hUU hVV
    (Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv X.hom Y.hom U V hUU hVV (x.val ⊗ₜ[ℂ] y.val))) = _
  rw [RectangleMixedClassProjection.rectangleMixedClassProjection_cycles, TensorProduct.map_tmul,
    Open.CycleIntrinsicClass.nativeOpenCechCycleQuotientClass_mk, Open.CycleIntrinsicClass.nativeOpenCechCycleQuotientClass_mk]

variable [(pullback X.hom Y.hom).IsSeparated]

theorem nativeRectangleMixedProjection_zero_of_sheafClass_zero
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (w : RectangleBoundaryShuffle.rectangleOrdinaryCech2 X.hom Y.hom U V)
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf (pullback X.hom Y.hom).sheaf).obj
      (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V) 2
      (Regular.BoundaryShuffle.regularTripleCechCochain (pullback X.hom Y.hom) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V) w) = 0)
    (hclass : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V)
      (Dual.UnitCechClasses.ringAdditiveSheaf (pullback X.hom Y.hom).sheaf) (RectangleClassDetection.rectangleOpenCover_covers X.hom Y.hom U V hcU hcV) 1
      (Regular.BoundaryShuffle.regularTripleCechCochain (pullback X.hom Y.hom) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover X.hom Y.hom U V) w) hw = 0) :
    nativeRectangleMixedProjection X Y U V hcU hcV hUU hVV
      (RectangleBoundaryShuffle.rectangleTripleShuffle X.hom Y.hom U V w) = 0 := by
  change TensorProduct.map _ _ (RectangleMixedClassProjection.rectangleMixedClassProjection X.hom Y.hom U V hUU hVV
    (RectangleBoundaryShuffle.rectangleTripleShuffle X.hom Y.hom U V w)) = 0
  rw [RectangleClassDetection.rectangleTripleShuffle_zero_of_sheafClass_zero X.hom Y.hom U V hU hV hUU hVV hcU hcV w hw hclass,
    map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RectangleDetector
