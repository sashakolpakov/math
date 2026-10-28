import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitDescentConvergence
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSurfacePersistence
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFormDescent

/-! # Concrete Split Persistence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitPersistence.CM

noncomputable section

/-! ThetaCycle: once arithmetic automorphy supplies the explicit fiber equations
on a common principal surface, construct the actual closed descents, apply
the full PairingContinuity statement, and obtain nonzero native cup evaluation. The
original total Schwartz input is retained in every coefficient equation. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.Matrix.Norms.Elementwise

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (T : InitialSetup.CM.InitialBallTheta K D)

theorem actual_split_persistence (hPairingContinuity : Persistence.CM.PairingContinuityInput.{0, 0, 0})
    (forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2)
    (hpure : ∀ n, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 (forms n).val)
    (hclosed : ∀ n, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (forms n) = 0)
    (hcoeff : ∀ n (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain) z,
      z ∈ D.ball.domain → (forms n).val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) =
        CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z)
    (N : ℕ) (S : Cm.PrincipalBallSurface K D.ball N)
    (hinitial : ∀ z w, S.projection z = S.projection w →
      BallFormDescent.CM.ballCoverFiberCovector K D.ball N S.surface.variety S.projection S.isBallCover 2 T.form z =
        BallFormDescent.CM.ballCoverFiberCovector K D.ball N S.surface.variety S.projection S.isBallCover 2 T.form w)
    (hfamily : ∀ n z w, S.projection z = S.projection w →
      BallFormDescent.CM.ballCoverFiberCovector K D.ball N S.surface.variety S.projection S.isBallCover 2 (forms n) z =
        BallFormDescent.CM.ballCoverFiberCovector K D.ball N S.surface.variety S.projection S.isBallCover 2 (forms n) w) :
    ∃ (n : ℕ)
      (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.surface.variety.analyticModel S.surface.variety.analyticSpace 2),
      CoverPullback.CM.ballCoverPullback K D.ball N S.surface.variety S.projection S.isBallCover 2 α.val = T.form ∧
      CoverPullback.CM.ballCoverPullback K D.ball N S.surface.variety S.projection S.isBallCover 2 β.val = forms n ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.surface.variety.analyticModel S.surface.variety.analyticSpace 2 0 α.val.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.surface.variety.analyticModel S.surface.variety.analyticSpace 2 0 β.val.val ∧
      SurfaceProjectivePairing.CM.projectiveSurfaceConjugatePairing S.surface α.val β.val ≠ 0 ∧
      S.surface.evaluate
        (Cm.cup S.surface.variety 2 2 (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 2 α)
          (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β))) ≠ 0 := by
  obtain ⟨a, ⟨ha, hap, hac⟩, _⟩ := BallFormDescent.CM.existsUnique_ball_form_descent K D.ball N
    S.surface.variety S.projection S.isBallCover 2 0 T.form T.pure T.closed hinitial
  have hd (n : ℕ) := BallFormDescent.CM.existsUnique_ball_form_descent K D.ball N S.surface.variety
    S.projection S.isBallCover 2 0 (forms n) (hpure n) (hclosed n) (hfamily n)
  choose b hb using fun n => (hd n).exists
  have hlim := ConcreteSplitDescentConvergence.CM.actual_normalized_split_descents_converge K D T forms hpure hcoeff N
    S.surface.variety S.projection S.isBallCover b a (fun n => (hb n).1) ha
  have hne : a ≠ 0 :=
    (BallFormDescent.CM.ball_descended_form_nonzero K D.ball N S.surface.variety S.projection S.isBallCover
      2 T.form a ha).mpr T.nonzero
  obtain ⟨n, hn⟩ := ConcreteSurfacePersistence.CM.l52_actual_surface_pairing hPairingContinuity S.surface a b hap hne hlim
  let α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.surface.variety.analyticModel S.surface.variety.analyticSpace 2 :=
    ⟨a, hac⟩
  let β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.surface.variety.analyticModel S.surface.variety.analyticSpace 2 :=
    ⟨b n, (hb n).2.2⟩
  exact ⟨n, α, β, ha, (hb n).1, hap, (hb n).2.1, hn,
    SurfaceProjectivePairing.CM.projective_surface_cup_evaluation_nonzero S.surface α β hap (hb n).2.1 hn⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitPersistence.CM
