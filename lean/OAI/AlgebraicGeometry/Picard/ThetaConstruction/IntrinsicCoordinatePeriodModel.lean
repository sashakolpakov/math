import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicProjectivePeriodData
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernPairing

/-! # Intrinsic Coordinate Period Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel.Geometric

noncomputable section

/-! A lattice-preserving tangent coordinate change makes the same
actual abelian variety an ThetaConstruction period model. The derivative is exactly
the inverse coordinate change, so the ample Chern pairing is retained. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)
    (e : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] DefinitionsIntegral.Tangent g)
    (he : ∀ v, v ∈ T.lattice ↔ e.symm v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

local instance nativeCoordinate_integral : IsIntegral A.toOver.left := A.variety.property
local instance nativeCoordinate_smooth : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance nativeCoordinate_realLie :
    LieGroup 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup A

def nativeCoordinatePeriodModel : PeriodModel.Geometric.AlgebraicPeriodModel T where
  abelian := A
  period := (RepresentationTheory.Theta.Geometric.Torus.LinearEquiv.torusLinearDiffeomorph (ProjectivePeriodData.Geometric.projectivePeriodData T) (IntrinsicProjectivePeriodData.Geometric.nativeProjectivePeriodData A L hL)
    e.symm (fun v => (he v).symm)).trans (IntrinsicProjectivePeriodData.Geometric.nativeProjectivePeriodDiffeomorph A L hL)
  period_add := by
    intro u v
    change IntrinsicProjectivePeriodData.Geometric.nativeProjectivePeriodDiffeomorph A L hL
      (RepresentationTheory.Theta.Geometric.Torus.LinearEquiv.torusLinearEquiv (ProjectivePeriodData.Geometric.projectivePeriodData T) (IntrinsicProjectivePeriodData.Geometric.nativeProjectivePeriodData A L hL)
        e.symm (fun w => (he w).symm) (u + v)) = _
    rw [map_add]
    exact IntrinsicProjectivePeriodData.Geometric.nativeProjectivePeriodDiffeomorph_add A L hL _ _

theorem nativeCoordinatePeriodModel_vector (v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    (nativeCoordinatePeriodModel A L hL T e he).vectorPeriod v =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (e.symm v) := rfl

theorem nativeCoordinatePeriodModel_differential (v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    (nativeCoordinatePeriodModel A L hL T e he).periodDifferential v = e.symm v := by
  have hlat : Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice
      (A := IntrinsicPeriodDifferential.Geometric.nativeComparisonTorus T) (B := AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.torus A) e.symm.toLinearMap :=
    fun v hv => (he v).mp hv
  have hlift : Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts
      (nativeCoordinatePeriodModel A L hL T e he).nativeQuotientComparison.toAddMonoidHom
      e.symm.toLinearMap := by
    intro w
    apply (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).injective
    change (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A)
        ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm
          ((nativeCoordinatePeriodModel A L hL T e he).periodAddEquiv (QuotientAddGroup.mk w))) =
      (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A) (QuotientAddGroup.mk (e.symm w))
    exact ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).apply_symm_apply
      ((nativeCoordinatePeriodModel A L hL T e he).periodAddEquiv
        (QuotientAddGroup.mk (show (ProjectivePeriodData.Geometric.projectivePeriodData T).space from w)))).trans
      (congrArg Additive.ofMul (nativeCoordinatePeriodModel_vector A L hL T e he
        (show (ProjectivePeriodData.Geometric.projectivePeriodData T).space from w)))
  have huniq := (Classical.choose_spec
    (nativeCoordinatePeriodModel A L hL T e he).existsUnique_nativePeriodLift).2
      e.symm.toLinearMap ⟨hlat, hlift⟩
  exact ((nativeCoordinatePeriodModel A L hL T e he).nativePeriodLift_eq_differential v).symm.trans
    (DFunLike.congr_fun huniq v).symm

theorem nativeCoordinatePeriodModel_chern
    (hH : ∀ u v, T.riemannForm (e u) (e v) = AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL u v)
    (l m : T.lattice) :
    AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L
      ((nativeCoordinatePeriodModel A L hL T e he).nativeIntegralPeriod l)
      ((nativeCoordinatePeriodModel A L hL T e he).nativeIntegralPeriod m) =
        (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ) := by
  let M := nativeCoordinatePeriodModel A L hL T e he
  have hperiod := AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_period A L hL (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m)
  have hform : AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL (M.nativeIntegralPeriod l).val (M.nativeIntegralPeriod m).val =
      T.riemannForm l.val m.val := by
    change AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL (M.periodDifferential l.val) (M.periodDifferential m.val) = _
    exact (congrArg₂ (fun u v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A => AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL u v)
      (nativeCoordinatePeriodModel_differential A L hL T e he l.val)
      (nativeCoordinatePeriodModel_differential A L hL T e he m.val)).trans
        ((hH (e.symm l.val) (e.symm m.val)).symm.trans
          (congrArg₂ (fun u v => T.riemannForm u v) (e.apply_symm_apply l.val) (e.apply_symm_apply m.val)))
  have hreal := hperiod.symm.trans ((congrArg Complex.im hform).trans (DefinitionsIntegral.Geometric.integralLatticeForm_riemann T l m))
  exact_mod_cast hreal

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel.Geometric
