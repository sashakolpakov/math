import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionFrames

/-! # Form Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormFrames

noncomputable section

/-! Actual holomorphic forms on a coordinate domain form a finite free module over actual holomorphic functions. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

instance formsFunctionSMul (U : Opens E) (n : ℕ) : SMul (FunctionPure.holomorphicFunctions U) (DeRhamComplex.forms E U n) where
  smul f a := CoefficientMem.holomorphicCoefficientsEquivForms U n
    (f • (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm a)

theorem formsFunctionSMul_coefficients (U : Opens E) (n : ℕ)
    (f : FunctionPure.holomorphicFunctions U) (a : DeRhamComplex.forms E U n) :
    (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm (f • a) =
      f • (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm a :=
  (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm_apply_apply _

instance formsFunctionModule (U : Opens E) (n : ℕ) : Module (FunctionPure.holomorphicFunctions U) (DeRhamComplex.forms E U n) :=
  Function.Injective.module (FunctionPure.holomorphicFunctions U)
    (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm.toLinearMap.toAddMonoidHom
    (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm.injective (formsFunctionSMul_coefficients U n)

def holomorphicCoefficientsFunctionEquivForms (U : Opens E) (n : ℕ) :
    CoefficientMem.holomorphicOpenCoefficients U n ≃ₗ[FunctionPure.holomorphicFunctions U] DeRhamComplex.forms E U n where
  toFun := CoefficientMem.holomorphicCoefficientsEquivForms U n
  invFun := (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm
  left_inv := (CoefficientMem.holomorphicCoefficientsEquivForms U n).left_inv
  right_inv := (CoefficientMem.holomorphicCoefficientsEquivForms U n).right_inv
  map_add' := (CoefficientMem.holomorphicCoefficientsEquivForms U n).map_add
  map_smul' f a := by
    change CoefficientMem.holomorphicCoefficientsEquivForms U n (f • a) =
      CoefficientMem.holomorphicCoefficientsEquivForms U n
        (f • (CoefficientMem.holomorphicCoefficientsEquivForms U n).symm (CoefficientMem.holomorphicCoefficientsEquivForms U n a))
    rw [LinearEquiv.symm_apply_apply]

theorem forms_function_smul_coefficients (U : Opens E) (n : ℕ)
    (f : FunctionPure.holomorphicFunctions U) (a : DeRhamComplex.forms E U n) (x : U) :
    ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n (f • a))) x =
      f.val x • ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n a)) x := by
  exact congrArg (fun c : CoefficientMem.holomorphicOpenCoefficients U n => c.val x)
    (formsFunctionSMul_coefficients U n f a)

def holomorphicOpenFormsBasis (U : Opens E) (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0)))
      (FunctionPure.holomorphicFunctions U) (DeRhamComplex.forms E U n) := by
  letI := Pure.CovectorComplexTopology.Holomorphic.pureCovectors_finiteDimensional (E := E) n
  letI : Module.Free ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) :=
    Module.Free.of_divisionRing ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0)
  exact (SectionFrames.holomorphicSectionsBasis U (Module.finBasis ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0))).map
    ((FunctionPure.holomorphicPureSectionEquiv U n).symm.trans (holomorphicCoefficientsFunctionEquivForms U n))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormFrames
