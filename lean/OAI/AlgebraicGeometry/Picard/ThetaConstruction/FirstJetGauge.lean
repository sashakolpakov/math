import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GaugeNormalization
import OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

/-! # First Jet Gauge -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Exact first jets of the primitive ThetaConstruction theta factor force an
infinitesimal translation preserving its bundle to have zero direction. -/

section
open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} (T : DefinitionsIntegral.MarkedPolarizedTorus dim E)
    (hE : E.transpose = -E)

theorem DefinitionsIntegral.MarkedPolarizedTorus.firstJetGauge_eq_zero (a : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) (c : (ProjectivePeriodData.Geometric.projectivePeriodData T).space → DualNumber ℂ)
    (hc : ∀ w, RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt c w) (hunit : IsUnit (c 0))
    (htrans : ∀ (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) w,
      c (w + l.val) * RepresentationTheory.Theta.Geometric.ScalarFirstJet.scalarFirstJet ((DefinitionsIntegral.MarkedPolarizedTorus.polarizationFactor T hE).value l) w a =
        TrivSqZeroExt.inl ((DefinitionsIntegral.MarkedPolarizedTorus.polarizationFactor T hE).value l w) * c w) : a = 0 := by
  apply T.dualNumberGauge_nonzero_reduction_eq_zero a c hc
    (isUnit_iff_ne_zero.mp (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hunit))
  intro l w
  have hj : IsUnit (TrivSqZeroExt.inl ((DefinitionsIntegral.MarkedPolarizedTorus.polarizationFactor T hE).value l w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr
      (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_ne_zero (DefinitionsIntegral.Geometric.integralLatticeBasis T) (DefinitionsIntegral.Geometric.integralLatticeForm T)
        T.lattice.subtype T.riemannForm l w))
  have hjet := RepresentationTheory.Theta.Geometric.GaugeFirstJet.polarizationAutomorphy_firstJet (DefinitionsIntegral.Geometric.integralLatticeBasis T) (DefinitionsIntegral.Geometric.integralLatticeForm T)
    T.lattice.subtype T.riemannForm l w a
  apply hj.mul_left_cancel
  calc
    _ = c (w + l.val) *
        (TrivSqZeroExt.inl ((DefinitionsIntegral.MarkedPolarizedTorus.polarizationFactor T hE).value l w) *
          (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * T.riemannForm l.val a))) := by ac_rfl
    _ = c (w + l.val) * RepresentationTheory.Theta.Geometric.ScalarFirstJet.scalarFirstJet ((DefinitionsIntegral.MarkedPolarizedTorus.polarizationFactor T hE).value l) w a :=
      congrArg (_ * ·) hjet.symm
    _ = _ := htrans l w

end

namespace FirstJetGauge.Geometric.MarkedPolarizedTorus

end FirstJetGauge.Geometric.MarkedPolarizedTorus

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
