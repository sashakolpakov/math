import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion
import OAI.RepresentationTheory.Theta.Geometric.Torus.LinearEquiv
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold

/-! # Intrinsic Projective Period Data -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicProjectivePeriodData.Geometric

noncomputable section

/-! The native exponential lattice of an actual ample abelian variety
is projective period data. Its holomorphic quotient map is the original
exponential uniformization, with its original topology and group law. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)

local instance nativeProjective_integral : IsIntegral A.toOver.left := A.variety.property
local instance nativeProjective_smooth : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance nativeProjectivePoints_compact : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  A.variety.presentation.complexPoints_compactSpace
local instance nativeProjectivePeriod_full : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A

def nativeProjectivePeriodData : RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData where
  space := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A
  periodIntegerLattice := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
  projective := by
    let : DiscreteTopology (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).toAddSubgroup := inferInstanceAs (DiscreteTopology (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))
    let : CompactSpace (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ⧸ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).toAddSubgroup) :=
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A).symm.compactSpace
    apply (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).toAddSubgroup).mpr
    refine ⟨AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL, AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_symmetry A L hL,
      AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_positive A L hL, ?_⟩
    intro u hu v hv
    obtain ⟨n, hn⟩ := AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods.nativeChernForm_integral A L ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨n, (AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_period A L hL
      (AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟨u, hu⟩)
      (AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟨v, hv⟩)).trans ?_⟩
    exact_mod_cast hn.symm

def nativeProjectivePeriodDiffeomorph :
    (nativeProjectivePeriodData A L hL).periodTorus ≃ₘ⟮
      𝓘(ℂ, (nativeProjectivePeriodData A L hL).space),
      𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver :=
  Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.diffeomorph
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_mdifferentiable ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A)
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph_symm_mdifferentiable ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A)

theorem nativeProjectivePeriodDiffeomorph_mk (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    nativeProjectivePeriodDiffeomorph A L hL (QuotientAddGroup.mk v) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) v := rfl

theorem nativeProjectivePeriodDiffeomorph_add
    (u v : (nativeProjectivePeriodData A L hL).periodTorus) :
    nativeProjectivePeriodDiffeomorph A L hL (u + v) =
      nativeProjectivePeriodDiffeomorph A L hL u * nativeProjectivePeriodDiffeomorph A L hL v :=
  congrArg Additive.toMul ((AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.nativePeriodAddEquiv A).map_add u v)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicProjectivePeriodData.Geometric
