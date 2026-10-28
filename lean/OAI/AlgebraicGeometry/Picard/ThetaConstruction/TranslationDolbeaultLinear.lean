import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationPrimitiveLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition
import OAI.RepresentationTheory.Theta.Geometric.DolbeaultQuotient

/-! # Translation Dolbeault Linear -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Actual translation potentials construct a complex-linear map into
the native closed Dolbeault forms and their scalar-derivative quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition OAI.RepresentationTheory.Theta.Geometric.DolbeaultQuotient

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultLinear_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultLinear_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationDbarForm_add (a b : DefinitionsIntegral.Tangent g) :
    M.translationDbarForm (a + b) = M.translationDbarForm a + M.translationDbarForm b := by
  apply AbelianModuli.ReferenceFamily.DolbeaultTransition.closedDbarForm_eq_of_local_restrictions _ _ M.localPeriodDomain M.mem_localPeriodDomain
  intro p
  let d := DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.localPeriodDomain p) 0
  let r := DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (show M.localPeriodDomain p ≤ ⊤ from le_top) (q := 1)
  have hp := congrArg d (M.localTranslationZeroForm_add a b p)
  have hd := map_add d (M.localTranslationZeroForm a p) (M.localTranslationZeroForm b p)
  have hr := map_add r (M.translationDbarForm a).val (M.translationDbarForm b).val
  exact (M.translationDbarForm_restrict (a + b) p).symm.trans
    (hp.trans (hd.trans ((congrArg₂ (· + ·)
      (M.translationDbarForm_restrict a p) (M.translationDbarForm_restrict b p)).trans hr.symm)))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationDbarForm_smul (c : ℂ) (a : DefinitionsIntegral.Tangent g) :
    M.translationDbarForm (c • a) = c • M.translationDbarForm a := by
  apply AbelianModuli.ReferenceFamily.DolbeaultTransition.closedDbarForm_eq_of_local_restrictions _ _ M.localPeriodDomain M.mem_localPeriodDomain
  intro p
  let d := DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.localPeriodDomain p) 0
  let r := DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (show M.localPeriodDomain p ≤ ⊤ from le_top) (q := 1)
  have hp := congrArg d (M.localTranslationZeroForm_smul c a p)
  have hd := map_smul d c (M.localTranslationZeroForm a p)
  have hr := map_smul r c (M.translationDbarForm a).val
  exact (M.translationDbarForm_restrict (c • a) p).symm.trans
    (hp.trans (hd.trans ((congrArg (fun t => c • t) (M.translationDbarForm_restrict a p)).trans hr.symm)))

def PeriodModel.Geometric.AlgebraicPeriodModel.translationDbarLinear : DefinitionsIntegral.Tangent g →ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) where
  toFun := M.translationDbarForm
  map_add' := M.translationDbarForm_add
  map_smul' := M.translationDbarForm_smul

def PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultLinear : DefinitionsIntegral.Tangent g →ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  (LinearMap.range (RepresentationTheory.Theta.Geometric.DolbeaultQuotient.globalDbarLinear (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))).mkQ.comp
    M.translationDbarLinear

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultLinear_holomorphic (a : DefinitionsIntegral.Tangent g) :
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.dolbeaultOneClassEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationDolbeaultLinear a) =
        RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
          (M.translationDbarForm a) := rfl

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
