import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteBallInvariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitPersistence
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallInvariantDescent

/-! # Concrete Principal Persistence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcretePrincipalPersistence.CM

noncomputable section

/-! Construct the common actual principal surface, descend the complete
normalized family, and apply full PairingContinuity to obtain a nonzero native cup
evaluation. No invariance, descent, or persistence hypothesis is added. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff _root_.Topology _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open Filter

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (T : InitialSetup.CM.InitialBallTheta K D) (hid : ∀ i, (v i).val 1 = true)

include hid

theorem exists_actual_principal_theta_persistence (hPairingContinuity : Persistence.CM.PairingContinuityInput.{0, 0, 0}) :
    ∃ (N : ℕ) (hN : 0 < N) (hDN : D.depth ∣ N)
      (forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2),
      (∀ n, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 (forms n).val ∧
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (forms n) = 0 ∧
        ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
          ∀ z ∈ D.ball.domain, (forms n).val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
            CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z) ∧
      (let _ := SmoothTopology.CM.smoothFormTopology HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2
       Tendsto forms atTop (𝓝 T.form)) ∧
      (let S := D.surface N hN hDN
       ∃ (n : ℕ) (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.surface.variety.analyticModel S.surface.variety.analyticSpace 2),
         CoverPullback.CM.ballCoverPullback K D.ball N S.surface.variety S.projection S.isBallCover 2 α.val = T.form ∧
         CoverPullback.CM.ballCoverPullback K D.ball N S.surface.variety S.projection S.isBallCover 2 β.val = forms n ∧
         Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.surface.variety.analyticModel S.surface.variety.analyticSpace 2 0 α.val.val ∧
         Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.surface.variety.analyticModel S.surface.variety.analyticSpace 2 0 β.val.val ∧
         SurfaceProjectivePairing.CM.projectiveSurfaceConjugatePairing S.surface α.val β.val ≠ 0 ∧
         S.surface.evaluate
           (Cm.cup S.surface.variety 2 2 (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 2 α)
             (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β))) ≠ 0) := by
  have hforms := ConcreteSplitBallForms.CM.exists_actual_split_ball_forms_converging K D T
  let forms := hforms.choose
  have hlevel := ConcreteBallInvariance.CM.exists_actual_ball_theta_invariant_level K D hid T
  let N := D.depth * hlevel.choose
  have hN : 0 < N := Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 3) D.depth_ge_three) hlevel.choose_spec.1
  have hDN : D.depth ∣ N := dvd_mul_right D.depth hlevel.choose
  have hLN : hlevel.choose ∣ N := dvd_mul_left hlevel.choose D.depth
  let S := D.surface N hN hDN
  have hi := hlevel.choose_spec.2 N hLN
  have hinitial := BallInvariantDescent.CM.ball_fiber_covectors_of_principal_invariance K D.ball N S.surface.variety
    S.projection S.isBallCover 2 T.form (fun g hg => (hi g hg).1)
  have hfamily (n : ℕ) := BallInvariantDescent.CM.ball_fiber_covectors_of_principal_invariance K D.ball N S.surface.variety
    S.projection S.isBallCover 2 (forms n) (fun g hg =>
      (hi g hg).2 n (forms n) (hforms.choose_spec.1 n).1 (hforms.choose_spec.1 n).2.2)
  have hp := ConcreteSplitPersistence.CM.actual_split_persistence K D T hPairingContinuity forms
    (fun n => (hforms.choose_spec.1 n).1) (fun n => (hforms.choose_spec.1 n).2.1)
    (fun n e z hz => (hforms.choose_spec.1 n).2.2 e e.property z hz) N S hinitial hfamily
  exact ⟨N, hN, hDN, forms, hforms.choose_spec.1, hforms.choose_spec.2, hp⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcretePrincipalPersistence.CM
