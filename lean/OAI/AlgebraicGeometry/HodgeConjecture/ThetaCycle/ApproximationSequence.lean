import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal
import OAI.Analysis.HodgeTheory.PairingContinuity

/-! # Approximation Sequence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationSequence.CM

noncomputable section

/-! ThetaCycle: a concrete sequence of admissible rational splittings whose
actual compact period projectors converge to the original ones. -/

open scoped Classical _root_.Topology _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open Filter _root_.Module

def approximationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem approximation_scale_positive (n : ℕ) : 0 < approximationScale n := by
  unfold approximationScale
  positivity

theorem approximation_scale_tendsto : Tendsto approximationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

def approximationSequence (n : ℕ) :
    PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair (approximationScale n) :=
  Classical.choice (D.approximate (approximationScale n) (approximation_scale_positive n))

def oldCompactPeriods : Fin D.places.count → Analysis.DifferentialForms.Coordinates.LocalApproximation.CompactPeriod :=
  fun τ => Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ)
    (Pi.basisFun K (Fin 2)) (fun i => FourSplittings.CM.initialThetaSigns K v i (D.places.representative τ))

def newCompactPeriods {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) :
    Fin D.places.count → Analysis.DifferentialForms.Coordinates.LocalApproximation.CompactPeriod :=
  fun τ => Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ)
    A.basis (fun i => FourSplittings.CM.newThetaSigns K v i (D.places.representative τ))

/-- This is the full native admissibility predicate used in PairingContinuity; its sign
inequalities are retained from the actual arithmetic construction. -/
theorem approximation_new_signs {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) :
    Analysis.HodgeTheory.PairingContinuity.NewSignsSplitting (HeckeCycles.ReferenceDatum.CM.embeddings K D.places) D.pair.a
      (fun i τ => FourSplittings.CM.newThetaSigns K v i (D.places.representative τ))
      (fun τ => -(HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ D.pair.delta).im) A.basis :=
  ⟨A.orthogonal, A.nondegenerate, A.orthocomplement, A.coefficient_signs⟩

theorem sequence_compact_periods_tendsto :
    Tendsto (fun n => newCompactPeriods K D (approximationSequence K D n))
      atTop (𝓝 (oldCompactPeriods K D)) := by
  apply tendsto_pi_nhds.mpr
  intro τ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hs : ∀ᶠ n in atTop, approximationScale n < ε :=
    approximation_scale_tendsto.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  exact ⟨N, fun n hn => ((approximationSequence K D n).compact_close τ).trans (hN n hn)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationSequence.CM
