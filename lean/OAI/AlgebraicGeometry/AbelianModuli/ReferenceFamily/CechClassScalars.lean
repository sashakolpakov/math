import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechComplexScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Analytification

/-! # Cech Class Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClassScalars

noncomputable section

/-! Scalar multiplication on original algebraic Cech cohomology is
represented by literal multiplication of its module cocycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {I : Type} (U : I → A.carrier.Opens)

def algebraicCechScalarMap (c : ℂ) : CechClasses.algebraicCechComplex A.variety U ⟶ CechClasses.algebraicCechComplex A.variety U :=
  (CategoryTheory.cechComplexFunctor U).map
    ((SheafOfModules.toSheaf A.carrier.ringCatSheaf).map
      (SheafCohomology.AffineH.Projective.globalSmulHom (HilbertConstruction.Line.Bundles.structureModule A.carrier) (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c))).hom

theorem algebraicCech_closed_smul (r : Γ(A.carrier, ⊤))
    (z : Γ(Cech.TermModules.cechTermModule A.carrier U 1, ⊤)) (hz : (Cech.ModuleDifferential.cechModuleDifferential A.carrier U 1).app ⊤ z = 0) :
    (Cech.ModuleDifferential.cechModuleDifferential A.carrier U 1).app ⊤ (r • z) = 0 := by
  have hs : (Cech.ModuleDifferential.cechModuleDifferential A.carrier U 1).app ⊤ (r • z) =
      r • (Cech.ModuleDifferential.cechModuleDifferential A.carrier U 1).app ⊤ z :=
    (HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp (Cech.ModuleDifferential.cechModuleDifferential A.carrier U 1) ⊤).map_smul r z
  rw [hs, hz, smul_zero]

theorem algebraicCechOneClass_scalar (c : ℂ) (z : Γ(Cech.TermModules.cechTermModule A.carrier U 1, ⊤))
    (hz : (Cech.ModuleDifferential.cechModuleDifferential A.carrier U 1).app ⊤ z = 0) :
    HomologicalComplex.homologyMap (algebraicCechScalarMap A U c) 1 (CechClasses.algebraicCechOneClass A.variety U z hz) =
      CechClasses.algebraicCechOneClass A.variety U (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c • z)
        (algebraicCech_closed_smul A U _ z hz) := by
  let K := CechClasses.algebraicCechComplex A.variety U
  let f := algebraicCechScalarMap A U c
  let x := Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates A.carrier U 1 z
  have hx := CechClasses.algebraicCechCoordinates_closed A.variety U 1 z hz
  have hfx := DivisorClass.Chern.Intrinsic.DescentCohomology.abelianCochainMap_closed f 0 x hx
  change HomologicalComplex.homologyMap f 1 (K.homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 K x hx)) = _
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 0 f x hx hfx]
  apply congrArg (K.homologyπ 1)
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
  erw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact (Cech.GlobalScalarCoordinates.cechGlobalModuleCoordinates_smul A.carrier U 1 (SheafCohomology.Sheaves.Projective.complexGlobalScalars A c) z).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClassScalars
