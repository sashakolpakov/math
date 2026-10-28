import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleMixedClassProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassZeroCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars

/-! # Cycle Intrinsic Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.CycleIntrinsicClass

noncomputable section

/-! The actual open-cover cycle quotient maps linearly to original
structure-sheaf H1. Its value is the literal regular Cech class, and
actual degree-zero boundaries are killed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {I : Type} (U : I → X.left.Opens) (hU : iSup U = ⊤)

local instance openCycleNativeH1Module : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule X

theorem openModuleCycle_regular
    (z : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U)) :
    RegularPair.Closed.RegularPairCocycle X.left U z.val := by
  have hz := (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_eq_zero_iff (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U z.val).mp z.property
  intro i j l
  exact hz i j l ((U i ⊓ U j) ⊓ U l)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

def nativeOpenCechCycleClass :
    LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 where
  toFun z := RegularPair.Closed.regularPairSheafClass X.left U hU z.val (openModuleCycle_regular X U z)
  map_add' x y := RegularPair.ClassAddition.regularPairSheafClass_add X.left U x.val y.val hU
    (openModuleCycle_regular X U x) (openModuleCycle_regular X U y)
  map_smul' c x := RegularPair.ClassScalars.regularPairSheafClass_globalScalar X.left U hU x.val (c • x).val
    (openModuleCycle_regular X U x) (openModuleCycle_regular X U (c • x))
    (ComplexConstants.complexGlobalSectionMap X c) (fun _ _ => rfl)

theorem nativeOpenCechCycleClass_boundary
    (s : Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) :
    nativeOpenCechCycleClass X U hU
      ⟨Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U s,
        LinearMap.congr_fun (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_comp_D0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) s⟩ = 0 := by
  let z : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) :=
    ⟨Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U s,
      LinearMap.congr_fun (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_comp_D0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) s⟩
  apply (RegularPair.ClassZeroCriterion.regularPairSheafClass_eq_zero_iff_primitive X.left U z.val hU
    (openModuleCycle_regular X U z)).mpr
  refine ⟨fun i => -s i, fun i j => ?_⟩
  change X.left.presheaf.map (homOfLE inf_le_right).op (s j) -
      X.left.presheaf.map (homOfLE inf_le_left).op (s i) =
    X.left.presheaf.map (homOfLE inf_le_left).op (-s i) -
      X.left.presheaf.map (homOfLE inf_le_right).op (-s j)
  erw [map_neg, map_neg]
  abel

def nativeOpenCechCycleQuotientClass :
    RectangleMixedClassProjection.openModuleCycleQuotient (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 :=
  (MixedComplexBoundaryProjection.cycleBoundarySubmodule (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U)
    (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U)).liftQ
      (nativeOpenCechCycleClass X U hU) (by
        intro z hz
        change nativeOpenCechCycleClass X U hU z = 0
        obtain ⟨s, hs⟩ := hz
        have he : z = ⟨Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U s,
            LinearMap.congr_fun (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_comp_D0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U) s⟩ :=
          Subtype.ext hs.symm
        rw [he]
        exact nativeOpenCechCycleClass_boundary X U hU s)

theorem nativeOpenCechCycleQuotientClass_mk
    (z : LinearMap.ker (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U)) :
    nativeOpenCechCycleQuotientClass X U hU
      ((MixedComplexBoundaryProjection.cycleBoundarySubmodule (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U)
        (Quotients.FiniteDescent.OpenCechShortComplex.Construction.CubeCech.openModuleCechD1 (Quotients.FiniteDescent.CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf X.hom) U)).mkQ z) =
      RegularPair.Closed.regularPairSheafClass X.left U hU z.val (openModuleCycle_regular X U z) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.CycleIntrinsicClass
