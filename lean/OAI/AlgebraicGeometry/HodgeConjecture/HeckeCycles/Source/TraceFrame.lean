import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TracePhaseCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames

/-! # Trace Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceFrame.CM

noncomputable section

/-! A full rational symplectic frame obtained from the actual number-field
tensor frame and trace-dual coordinates. Its dimension agrees with the
original source coordinates by the constructed linear equivalences. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

abbrev Index := Finite.AdelicTestCoordinates.CM.Index (QuadraticConjugation.CM.Field.RealField E) 3

def fieldFrame : GeometricSource.CM.Vec E ≃ₗ[ℚ] ((Fin 3 → QuadraticConjugation.CM.Field.RealField E) × (Fin 3 → QuadraticConjugation.CM.Field.RealField E)) :=
  (TensorAction.CM.tensorEquiv E C).restrictScalars ℚ |>.trans
    (((GlobalFrames.CM.rational E C).coordinates.restrictScalars ℚ).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) ℚ (QuadraticConjugation.CM.Field.RealField E)))

def rational : GeometricSource.CM.Vec E ≃ₗ[ℚ] ((Index E → ℚ) × (Index E → ℚ)) :=
  (fieldFrame E C).trans (TracePhaseCoordinates.CM.phase (QuadraticConjugation.CM.Field.RealField E) 3)

theorem pairing (x y : GeometricSource.CM.Vec E) :
    (∑ i, ((CM.rational E C x).1 i * (CM.rational E C y).2 i -
      (CM.rational E C y).1 i * (CM.rational E C x).2 i)) =
        Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) := by
  change (∑ i, ((TracePhaseCoordinates.CM.phase (QuadraticConjugation.CM.Field.RealField E) 3 (fieldFrame E C x)).1 i *
    (TracePhaseCoordinates.CM.phase (QuadraticConjugation.CM.Field.RealField E) 3 (fieldFrame E C y)).2 i -
    (TracePhaseCoordinates.CM.phase (QuadraticConjugation.CM.Field.RealField E) 3 (fieldFrame E C y)).1 i *
    (TracePhaseCoordinates.CM.phase (QuadraticConjugation.CM.Field.RealField E) 3 (fieldFrame E C x)).2 i)) = _
  rw [TracePhaseCoordinates.CM.phase_pairing]
  change Algebra.trace ℚ (QuadraticConjugation.CM.Field.RealField E)
    (∑ i : Fin 3, ((GlobalFrames.CM.rational E C).coordinates
        (TensorPairing.CM.tensorVector E C x) (.inl i) *
      (GlobalFrames.CM.rational E C).coordinates
        (TensorPairing.CM.tensorVector E C y) (.inr i) -
      (GlobalFrames.CM.rational E C).coordinates
        (TensorPairing.CM.tensorVector E C y) (.inl i) *
      (GlobalFrames.CM.rational E C).coordinates
        (TensorPairing.CM.tensorVector E C x) (.inr i))) = _
  rw [← DiagonalFrame.CM.TracePairing.standard_pairing,
    (GlobalFrames.CM.rational E C).preserves,
    TensorPairing.CM.source_pairing]

include C in
theorem index_card : Fintype.card (GeometricSource.CM.Positions E places) = Fintype.card (Index E) := by
  have h := (C.rational.symm.trans (CM.rational E C)).finrank_eq
  simp only [Module.finrank_prod, Module.finrank_pi] at h
  omega

def indexEquiv : GeometricSource.CM.Positions E places ≃ Index E := Fintype.equivOfCardEq (index_card E C)

def reindexed : GeometricSource.CM.Vec E ≃ₗ[ℚ] ((GeometricSource.CM.Positions E places → ℚ) × (GeometricSource.CM.Positions E places → ℚ)) :=
  (CM.rational E C).trans ((LinearEquiv.funCongrLeft ℚ ℚ (indexEquiv E C)).prodCongr
    (LinearEquiv.funCongrLeft ℚ ℚ (indexEquiv E C)))

theorem reindexed_pairing (x y : GeometricSource.CM.Vec E) :
    (∑ i, ((reindexed E C x).1 i * (reindexed E C y).2 i -
      (reindexed E C y).1 i * (reindexed E C x).2 i)) =
        Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) := by
  change (∑ i, ((CM.rational E C x).1 (indexEquiv E C i) *
    (CM.rational E C y).2 (indexEquiv E C i) -
    (CM.rational E C y).1 (indexEquiv E C i) * (CM.rational E C x).2 (indexEquiv E C i))) = _
  exact ((indexEquiv E C).sum_comp (fun i => (CM.rational E C x).1 i *
    (CM.rational E C y).2 i - (CM.rational E C y).1 i * (CM.rational E C x).2 i)).trans
      (pairing E C x y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceFrame.CM
