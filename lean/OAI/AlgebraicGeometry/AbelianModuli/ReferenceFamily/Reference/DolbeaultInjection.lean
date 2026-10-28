import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TranslationDolbeaultLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualHolomorphicInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DiscreteComplexKernel

/-! # Dolbeault Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual complex-linear Dolbeault parameter map is injective.
Its kernel is a complex vector space contained in the proved discrete
integral dual-lattice kernel of its holomorphic exponential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.dolbeaultInjection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.dolbeaultInjection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.dolbeaultInjection_functionCohomologyGroup :
    AddCommGroup (CategoryTheory.Sheaf.H
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance AlgebraicModel.ReferenceAlgebraicModel.dolbeaultInjection_unitCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem AlgebraicModel.ReferenceAlgebraicModel.translationDolbeaultLinear_injective : Function.Injective M.translationDolbeaultLinear := by
  let : DiscreteTopology F.dualLattice.toAddSubgroup := F.dualLattice_discrete
  apply DiscreteComplexKernel.complexLinear_injective_of_discrete_kernel F.dualLattice.toAddSubgroup M.translationDolbeaultLinear
  intro a ha
  have hzq : (Submodule.Quotient.mk (M.translationDbarForm a) :
      RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) = 0 := ha
  obtain ⟨s, hs⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzq
  have he : RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationDbarForm a) = 0 :=
    (congrArg (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) hs).symm.trans
      (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass_derivative (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) s)
  have hz : M.translationHolomorphicClass a = 0 :=
    (congrArg (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) he).trans
      (map_zero (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)))
  exact M.translationHolomorphicClass_zero_mem_dual a hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
