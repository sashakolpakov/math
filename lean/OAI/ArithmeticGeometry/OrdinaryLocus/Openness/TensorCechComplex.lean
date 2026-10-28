import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechDifferentials
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleBaseChangeComplex

/-! # Tensor Cech Complex -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechComplex.Construction

noncomputable section

/-! The tensor of a finite-cover Cech complex is its complex of tensor-valued local sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped TensorProduct

universe u

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {X : TopCat.{u}} (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → Opens X)

theorem tensorCechD1_comp_D0 :
    (TensorCechDifferentials.Construction.tensorCechD1 (K := K) F U).comp (TensorCechDifferentials.Construction.tensorCechD0 F U) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates0 (K := K) F U).surjective z
  have hd0 := LinearMap.congr_fun (TensorCechDifferentials.Construction.cechBaseChangeCoordinates_d0 (K := K) F U) x
  have hd1 := LinearMap.congr_fun (TensorCechDifferentials.Construction.cechBaseChangeCoordinates_d1 (K := K) F U)
    ((OpenCechDegreeZero.Construction.openModuleCechD0 F U).baseChange K x)
  change CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates1 F U ((OpenCechDegreeZero.Construction.openModuleCechD0 F U).baseChange K x) =
    TensorCechDifferentials.Construction.tensorCechD0 F U (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates0 F U x) at hd0
  change CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates2 F U
      ((OpenCechShortComplex.Construction.openModuleCechD1 F U).baseChange K ((OpenCechDegreeZero.Construction.openModuleCechD0 F U).baseChange K x)) =
    TensorCechDifferentials.Construction.tensorCechD1 F U (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates1 F U ((OpenCechDegreeZero.Construction.openModuleCechD0 F U).baseChange K x)) at hd1
  have hz := congrArg (LinearMap.baseChange K) (OpenCechShortComplex.Construction.openModuleCechD1_comp_D0 F U)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at hz
  change TensorCechDifferentials.Construction.tensorCechD1 F U (TensorCechDifferentials.Construction.tensorCechD0 F U (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates0 F U x)) = 0
  rw [← hd0, ← hd1]
  have hz' := LinearMap.congr_fun hz x
  change (OpenCechShortComplex.Construction.openModuleCechD1 F U).baseChange K ((OpenCechDegreeZero.Construction.openModuleCechD0 F U).baseChange K x) = 0 at hz'
  rw [hz', map_zero]

abbrev tensorCechShortComplex : ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.moduleCatMk (TensorCechDifferentials.Construction.tensorCechD0 F U) (TensorCechDifferentials.Construction.tensorCechD1 F U) (tensorCechD1_comp_D0 F U)

def tensorCechComplexIso :
    ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K (OpenCechShortComplex.Construction.openModuleCechShortComplex F U) ≅ tensorCechShortComplex F U :=
  ShortComplex.isoMk
    (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates0 F U).toModuleIso
    (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates1 F U).toModuleIso
    (CechBaseChangeCoordinates.Construction.cechBaseChangeCoordinates2 F U).toModuleIso
    (by
      apply ModuleCat.hom_ext
      exact (TensorCechDifferentials.Construction.cechBaseChangeCoordinates_d0 F U).symm)
    (by
      apply ModuleCat.hom_ext
      exact (TensorCechDifferentials.Construction.cechBaseChangeCoordinates_d1 F U).symm)

def tensorCechHomologyIso :
    (ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K (OpenCechShortComplex.Construction.openModuleCechShortComplex F U)).homology ≅
      (tensorCechShortComplex F U).homology :=
  ShortComplex.homologyMapIso (tensorCechComplexIso F U)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechComplex.Construction
