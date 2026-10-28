import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationDolbeaultLinear
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DualHolomorphicInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DiscreteComplexKernel

/-! # Dolbeault Injection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual complex-linear Dolbeault parameter map is injective.
Its kernel is a complex vector space contained in the proved discrete
integral dual-lattice kernel of its holomorphic exponential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DiscreteComplexKernel

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.dolbeaultInjection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dolbeaultInjection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dolbeaultInjection_functionCohomologyGroup :
    AddCommGroup (CategoryTheory.Sheaf.H
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dolbeaultInjection_unitCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultLinear_injective : Function.Injective M.translationDolbeaultLinear := by
  let : DiscreteTopology T.integralDualLattice.toAddSubgroup := T.integralDualLattice_discrete
  apply AbelianModuli.ReferenceFamily.DiscreteComplexKernel.complexLinear_injective_of_discrete_kernel T.integralDualLattice.toAddSubgroup M.translationDolbeaultLinear
  intro a ha
  have hzq : (Submodule.Quotient.mk (M.translationDbarForm a) :
      RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) = 0 := ha
  obtain ⟨s, hs⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzq
  have he : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationDbarForm a) = 0 :=
    (congrArg (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) hs).symm.trans
      (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass_derivative (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) s)
  have hz : M.translationHolomorphicClass a = 0 :=
    (congrArg (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) he).trans
      (map_zero (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)))
  exact M.translationHolomorphicClass_zero_mem_dual a hz

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
