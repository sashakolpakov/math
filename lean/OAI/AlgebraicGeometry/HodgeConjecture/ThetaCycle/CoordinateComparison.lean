import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Symplectic
import OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport

/-! # Coordinate Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateComparison.CM

noncomputable section

/-! The accepted rational and complex coordinate fields determine the same
scalar extension as the native paired-coordinate construction. This lets its
proved isotropy and positivity results be used for the exact HeckeCycles period. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def sumCoordinates (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) :
    HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[ℚ] (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℚ) :=
  C.rational.trans (LinearEquiv.sumArrowLequivProdArrow
    (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℚ ℚ).symm

omit [IsGalois ℚ K] in
theorem sumCoordinates_pairing (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (sumCoordinates K C x) (sumCoordinates K C y) =
      RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm K (C.delta * C.a) (Matrix.diagonal ![1, 1, B.b]) x y := by
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal]
  change _ = Algebra.trace ℚ K (C.delta * C.a * HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
  rw [C.symplectic]
  apply Finset.sum_congr rfl
  intro j _
  change (C.rational x).1 j * (C.rational y).2 j - (C.rational x).2 j * (C.rational y).1 j = _
  ring

theorem native_complex_coordinates (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (u : Lagrangians.CM.pairedAmbient K places) :
    C.complex ((Symplectic.CM.galoisToPaired K places).symm u) =
      (LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ ℂ)
        (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
          (sumCoordinates K C) u) := by
  obtain ⟨x, rfl⟩ := (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification K
    (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)).surjective u
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
      rw [RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates_tmul K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
        (sumCoordinates K C) c x,
        RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification_tmul K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) c x,
        ← Symplectic.CM.galoisToPaired_embedding, map_smul, LinearEquiv.symm_apply_apply,
        map_smul, C.extends_rational, map_smul]
      rfl

theorem coordinate_pairing_preserved (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (u v : Lagrangians.CM.pairedAmbient K places) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing
      (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
        (sumCoordinates K C) u)
      (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
        (sumCoordinates K C) v) =
      Geometry.ComplexBall.PrescribedSignsB.tracePairing (Lagrangians.CM.pairedBallForm K B places)
        (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (C.delta * C.a)) u v := by
  exact RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.rationalCoordinates_preserves_pairing K (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places)
    C.delta C.a C.delta_imaginary C.a_real (Matrix.diagonal ![1, 1, B.b])
    (NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_hermitian B.b B.conjugate_b)
    (sumCoordinates K C) (sumCoordinates_pairing K C) u v

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateComparison.CM
