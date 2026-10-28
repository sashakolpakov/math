import OAI.AlgebraicGeometry.ComplexMultiplication.ChainFunctor
import OAI.AlgebraicTopology.Singular.CohomologyTo
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.Complex.Module

/-! # Singular Base Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularBaseChange

noncomputable section

/-! # Rational-to-complex base change for the actual singular homology -/

open _root_.CategoryTheory Limits _root_.AlgebraicTopology

/-- The exact extension-of-scalars functor for the original coefficient inclusion. -/
abbrev rationalComplexScalars : ModuleCat.{0} ℚ ⥤ ModuleCat.{0} ℂ :=
  ModuleCat.extendScalars (algebraMap ℚ ℂ)

instance CMSingularBaseChange.localInstance1 : PreservesFiniteLimits rationalComplexScalars :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

instance CMSingularBaseChange.localInstance2 : rationalComplexScalars.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The coefficient object `ℂ ⊗_ℚ ℚ` is canonically the usual complex coefficient module. -/
def rationalComplexCoefficientIso :
    rationalComplexScalars.obj (ModuleCat.of ℚ ℚ) ≅ ModuleCat.of ℂ ℂ :=
  by
    letI : Algebra ℚ ℂ := (algebraMap ℚ ℂ).toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ).toModuleIso

/-- The actual singular chain complexes commute with extension from rational to complex
coefficients. The boundary is the original singular boundary on both sides. -/
def rationalComplexSingularChainIso (Y : TopCat.{0}) :
    (rationalComplexScalars.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.Singular.Cohomology.SingularChainComplex ℚ Y) ≅ AlgebraicTopology.Singular.Cohomology.SingularChainComplex ℂ Y :=
  ChainFunctor.chainFunctorIso rationalComplexScalars (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) ≪≫
    ((SSet.chainComplexFunctor (ModuleCat ℂ)).mapIso rationalComplexCoefficientIso).app
      (TopCat.toSSet.obj Y)

/-- The original rational singular homology extends to the original complex singular homology. -/
def rationalComplexSingularHomologyIso (Y : TopCat.{0}) (n : ℕ) :
    rationalComplexScalars.obj (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n) ≅ AlgebraicTopology.Singular.Cohomology.Homology ℂ Y n :=
  (((AlgebraicTopology.Singular.Cohomology.SingularChainComplex ℚ Y).sc n).mapHomologyIso
    rationalComplexScalars).symm ≪≫
    HomologicalComplex.homologyMapIso (rationalComplexSingularChainIso Y) n

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularBaseChange
