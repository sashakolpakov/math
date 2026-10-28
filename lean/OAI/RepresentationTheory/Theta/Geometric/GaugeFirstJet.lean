import OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJet
import OAI.RepresentationTheory.Theta.Geometric.GaugeDerivativeHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection

/-! # Gauge First Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

noncomputable section

/-! First jets of the original theta gauges and of their polarization
automorphy factor, with the exact infinitesimal coefficient. -/

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] {L I : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]

theorem polarizationAutomorphy_firstJet (b : Module.Basis I ℤ L)
    (B : LinearMap.BilinForm ℤ L) (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (l : L) (z a : V) :
    ScalarFirstJet.scalarFirstJet (PolarizationAutomorphy.polarizationAutomorphy b B e H l) z a =
      TrivSqZeroExt.inl (PolarizationAutomorphy.polarizationAutomorphy b B e H l z) *
        (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * H (e l) a)) := by
  apply TrivSqZeroExt.ext
  · simp [ScalarFirstJet.scalarFirstJet]
  · change fderiv ℂ (PolarizationAutomorphy.polarizationAutomorphy b B e H l) z a =
      PolarizationAutomorphy.polarizationAutomorphy b B e H l z * (0 + (Real.pi : ℂ) * H (e l) a) +
        0 * (1 + 0)
    simpa only [zero_add, zero_mul, add_zero] using PolarizationConnection.polarizationAutomorphy_fderiv H b B e l z a

end

namespace CM.Torus.AutomorphicTheta

open OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

theorem consecutiveGauge_firstJet_translates (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (hdeg : G.degree = F.degree + 1)
    (i : Fin (F.projectiveDimension + 1)) (j : Fin (G.projectiveDimension + 1))
    (l : Φ.periodIntegerLattice) (z a : Φ.space)
    (hi : F.coordinate i z ≠ 0) (hJ : DifferentiableAt ℂ (J.value l) z) :
    ScalarFirstJet.scalarFirstJet (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i j) (z + l.val) a =
      ScalarFirstJet.scalarFirstJet (J.value l) z a * ScalarFirstJet.scalarFirstJet (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i j) z a :=
  ScalarFirstJet.scalarFirstJet_translates _ _ l.val z a
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i j z hi) hJ
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates F G hdeg i j l)

end CM.Torus.AutomorphicTheta

end

end OAI.RepresentationTheory.Theta.Geometric.GaugeFirstJet
