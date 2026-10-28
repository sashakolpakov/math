import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GaugeNormalization
import OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

/-! # First Jet Gauge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Exact first-jet covariance of the original polarization factor
forces the infinitesimal translation direction to vanish. -/

open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

theorem Fiber.ReferenceAnalyticFiber.firstJetGauge_eq_zero (a : F.periodData.space)
    (c : F.periodData.space → DualNumber ℂ)
    (hc : ∀ w, RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt c w) (hunit : IsUnit (c 0))
    (htrans : ∀ (l : F.periodData.periodIntegerLattice) w,
      c (w + l.val) * RepresentationTheory.Theta.Geometric.ScalarFirstJet.scalarFirstJet ((F.polarizationFactor hP).value l) w a =
        TrivSqZeroExt.inl ((F.polarizationFactor hP).value l w) * c w) : a = 0 := by
  apply F.dualNumberGauge_nonzero_reduction_eq_zero a c hc
    (isUnit_iff_ne_zero.mp (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hunit))
  intro l w
  have H := htrans (F.integralLatticeEquiv l) w
  change c (w + F.latticeEmbedding l) *
      RepresentationTheory.Theta.Geometric.ScalarFirstJet.scalarFirstJet (F.polarizationAutomorphy hP
        (F.integralLatticeEquiv.symm (F.integralLatticeEquiv l))) w a =
    TrivSqZeroExt.inl (F.polarizationAutomorphy hP
      (F.integralLatticeEquiv.symm (F.integralLatticeEquiv l)) w) * c w at H
  simp only [LinearEquiv.symm_apply_apply] at H
  have hj : IsUnit (TrivSqZeroExt.inl (F.polarizationAutomorphy hP l w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr
      (RepresentationTheory.Theta.Geometric.PolarizationAutomorphy.polarizationAutomorphy_ne_zero (P.referenceBasis hP) P.integralForm F.latticeEmbedding F.form l w))
  have hjet := RepresentationTheory.Theta.Geometric.GaugeFirstJet.polarizationAutomorphy_firstJet (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding F.form l w a
  apply hj.mul_left_cancel
  calc
    _ = c (w + F.latticeEmbedding l) *
        (TrivSqZeroExt.inl (F.polarizationAutomorphy hP l w) *
          (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a))) := by ac_rfl
    _ = c (w + F.latticeEmbedding l) *
        RepresentationTheory.Theta.Geometric.ScalarFirstJet.scalarFirstJet (F.polarizationAutomorphy hP l) w a := congrArg (_ * ·) hjet.symm
    _ = _ := H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
