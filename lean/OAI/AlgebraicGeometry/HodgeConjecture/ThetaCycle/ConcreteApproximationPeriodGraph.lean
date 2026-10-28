import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricFrame
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicIndexedGraphs
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod

/-! # Concrete Approximation Period Graph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationPeriodGraph.CM

noncomputable section

/-! The period of every actual approximation on the fixed native tensor
space is the fixed original rational symplectic transform of its period
in the original source coordinates. Thus the finite-input transition is
independent of the approximation. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

abbrev originalNativeSymplecticTransition :=
  SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place
    (fun j => (D.initialPeriods j).coordinates) D.initial_coefficients

def approximationIndexedPeriod (z : D.ball.Domain) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K D.places) :=
  IntrinsicIndexedGraphs.CM.nativeIndexedPeriod (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
    (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)

theorem approximation_total_graph_as_frame (z : D.ball.Domain) (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    ∃ u : PeriodTotal.CM.TotalPositions K D.places → ℂ,
      ComplexTransition.CM.complexTensorBasisChange K A.basis
        (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u) =
      TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (D.initialPeriods j).coordinates)
        (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) x := by
  let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val)
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator Z.matrix
  let y := J⁻¹.mulVec x
  have hJ : J.mulVec y = x := by
    change J.mulVec (J⁻¹.mulVec x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).denominator_det_isUnit Z), Matrix.one_mulVec]
  let u := AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
    (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (A.periods j).coordinates) Z y)
  have hr : AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u =
      TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (A.periods j).coordinates) Z y :=
    AdaptedTotal.CM.total_native_frame_recovers_graph K A.periods z.val z.property y
  have ht := MovingTotalPeriod.CM.approximation_total_graph K D A z.val y
  have hc := congrArg (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (D.initialPeriods j).coordinates)
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val)) hJ
  exact ⟨u, (congrArg (ComplexTransition.CM.complexTensorBasisChange K A.basis) hr).trans (ht.symm.trans hc)⟩

theorem approximation_native_total_graph_relation (z : D.ball.Domain)
    (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    let α := (originalNativeSymplecticTransition K D hid).val.map (algebraMap ℚ ℂ) *ᵥ
      Sum.elim ((MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val).matrix.mulVec x) x
    (approximationIndexedPeriod K D A hid z).matrix.mulVec (fun i => α (.inr i)) =
      fun i => α (.inl i) := by
  let w := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (D.initialPeriods j).coordinates)
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) x
  have hrec := approximation_total_graph_as_frame K D A z x
  let u := hrec.choose
  have hf := ConcreteApproximationGeometricFrame.CM.exists_actual_approximation_geometric_frame K D A hid
  have hg := (congrArg (ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid) hrec.choose_spec).symm.trans
    (hf.choose_spec z u)
  have ht := (ConcreteApproximationComplexComponents.CM.approximation_original_complex_transition K D A hid w).trans hg
  have hp := IntrinsicIndexedGraphs.CM.native_indexed_graph_equation (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (SourceComponents.CM.directSourceFrames K D.pair) (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
    ((originalNativeSymplecticTransition K D hid).val.map (algebraMap ℚ ℂ) *ᵥ
      ComplexTransition.CM.totalComplexCoordinates K (fun j => (D.initialPeriods j).coordinates) w) (hf.choose u) ht
  simpa only [w, TotalPeriodGraphs.CM.total_graph_coordinates] using! hp

theorem approximation_native_period_transform (z : D.ball.Domain) :
    approximationIndexedPeriod K D A hid z =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (originalNativeSymplecticTransition K D hid)).transformSiegel
        (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) := by
  apply IndexedGraphRelation.CM.symplectic_period_eq_of_graph
  intro x
  exact approximation_native_total_graph_relation K D A hid z x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationPeriodGraph.CM
