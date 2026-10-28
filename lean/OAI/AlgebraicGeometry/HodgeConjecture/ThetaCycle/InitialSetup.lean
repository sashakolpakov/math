import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalBallForms

/-! # Initial Setup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialSetup.CM

noncomputable section

/-!
ThetaCycle: assemble the constructed principal surface family and four-pattern
period data with one fixed, nonzero total theta input. The actual top form
here is on the common ball; descent to the principal surfaces remains a
separate construction.
-/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}

/-- Output data, derived from the actual initial periods. The input is a
single total finite Schwartz function, retained in the Hessian equation. -/
structure InitialBallTheta (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) where
  input : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K D.places) (HeckeCycles.GeometricSource.CM.Positions K D.places))
  form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2
  pure : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 form.val
  closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0
  nonzero : form ≠ 0
  coefficient : ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart),
    e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain → ∀ z ∈ D.ball.domain,
      form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
        InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) input z

theorem initial_ball_theta_exists (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) :
    Nonempty (InitialBallTheta K D) := by
  have hz : (0 : HeckeCycles.GeometricSource.CM.BallChart) ∈ D.ball.domain := by
    simpa [HeckeCycles.GeometricSource.CM.BallDatum.domain] using D.ball.negative
  obtain ⟨Φ, form, hp, hc, hn, he⟩ := TotalBallForms.CM.exists_nonzero_total_ball_top_form K
    (D.initialPeriods 0) (D.initialPeriods 1) ⟨0, hz⟩
  exact ⟨⟨Φ, form, hp, hc, hn, he⟩⟩

/-- Concrete initial geometric and theta data from the original arithmetic
conditions and the full named moduli prerequisite. -/
theorem exists_initial_surface_theta_setup (hReferenceFamily : Moduli.CM.ReferenceFamilyInput)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hb : ∀ τ, ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hi : ∀ i, (v i).val 1 = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (Nbase : ℕ) (hNbase : 0 < Nbase) :
    ∃ D : PeriodTotal.CM.FourPeriodSetup K v Nbase, Nonempty (InitialBallTheta K D) := by
  obtain ⟨D⟩ := PeriodTotal.CM.exists_four_period_setup K hReferenceFamily v hb hi hother Nbase hNbase
  exact ⟨D, initial_ball_theta_exists K D⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialSetup.CM
