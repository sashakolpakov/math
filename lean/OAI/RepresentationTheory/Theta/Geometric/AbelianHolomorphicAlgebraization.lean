import OAI.RepresentationTheory.Theta.Geometric.GroupHolomorphicLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage

/-! # Abelian Holomorphic Algebraization -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianHolomorphicAlgebraization

noncomputable section

/-! Every pure holomorphic Betti class of an actual complex abelian
variety has a constructed algebraic one-form with exactly that class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic
attribute [local instance] InvariantFormsSmooth.nativeGroupRealLie InvariantFormsSmooth.nativeGroupComplexLie

variable (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance : IsIntegral A.toOver.left := A.variety.property
local instance : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance : A.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated A.variety

def abelianPureCovectorAlgebraicLift :
    Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule A.variety.analyticModel 1 0 →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms A.toOver :=
  (GroupHolomorphicLift.groupHolomorphicAlgebraicLift A.toOver).comp
    (InvariantHolomorphicDimension.invariantHolomorphicChartEquiv A.variety.analyticModel A.variety.analyticSpace).symm.toLinearMap

theorem abelianPureCovectorAlgebraicLift_class
    (a : Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule A.variety.analyticModel 1 0) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass A.variety (abelianPureCovectorAlgebraicLift A a) =
      AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1 a.val := by
  have h : AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization A.variety (abelianPureCovectorAlgebraicLift A a) =
      AlgebraicGeometry.AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1
        ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1).symm a.val) := by
    apply Subtype.ext
    exact GroupHolomorphicLift.groupHolomorphicAlgebraicLift_realization A.toOver
      ((InvariantHolomorphicDimension.invariantHolomorphicChartEquiv A.variety.analyticModel A.variety.analyticSpace).symm a)
  change (A.variety.deRhamBettiIso 1).hom
    (A.variety.deRhamClass 1 (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization A.variety (abelianPureCovectorAlgebraicLift A a))) = _
  rw [h]
  rfl

def abelianPureBettiCovector :
    A.variety.pureBettiSubspace 1 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule A.variety.analyticModel 1 0 where
  toFun a := ⟨(AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1).symm a.val, by
    apply (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 1 0 _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact a.property⟩
  map_add' a b := Subtype.ext ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1).symm.map_add a.val b.val)
  map_smul' c a := Subtype.ext ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1).symm.map_smul c a.val)

def abelianPureBettiAlgebraicLift :
    A.variety.pureBettiSubspace 1 0 →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms A.toOver :=
  (abelianPureCovectorAlgebraicLift A).comp (abelianPureBettiCovector A)

theorem abelianPureBettiAlgebraicLift_class (a : A.variety.pureBettiSubspace 1 0) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass A.variety (abelianPureBettiAlgebraicLift A a) = a.val := by
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass A.variety (abelianPureCovectorAlgebraicLift A (abelianPureBettiCovector A a)) = _
  rw [abelianPureCovectorAlgebraicLift_class]
  exact (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1).apply_symm_apply a.val

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianHolomorphicAlgebraization
