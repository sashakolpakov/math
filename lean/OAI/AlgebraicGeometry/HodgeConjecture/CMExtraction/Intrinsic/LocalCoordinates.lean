import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitaryPhase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalCoordinateIntegral

/-! # Local Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalCoordinates

noncomputable section

/-! A named native local coordinate matrix retains the fixed rational
basis. Its integrality bound is chosen before the prime. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (v : Multiplicity.Odd.Sign E)

include hP

theorem nativeTraceCoefficient_ne_zero : P.imaginaryScalar * Multiplicity.nativeCoefficient E P v ≠ 0 := by
  rw [Multiplicity.native_orientedCoefficient E P hP v]
  exact neg_ne_zero.mpr (Multiplicity.Odd.imaginaryCoefficient_ne_zero E v)

theorem nativeTraceCoefficient_conjugate :
    NumberField.IsCMField.complexConj E (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) =
      -(P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) := by
  rw [Multiplicity.native_orientedCoefficient E P hP v]
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (-Multiplicity.Odd.imaginaryCoefficient E v) = - -Multiplicity.Odd.imaginaryCoefficient E v
  rw [map_neg, Multiplicity.Odd.imaginaryCoefficient_conjugate]

variable
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

def nativeLocalCoordinateMatrix
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
    (σ : Fin s → E →ₐ[ℚ] K) (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E K σ)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) K :=
  RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E K σ hσ (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v)
    (nativeTraceCoefficient_ne_zero E P hP v) (nativeTraceCoefficient_conjugate E P hP v)
    (Multiplicity.nativeMatrix E P) (Multiplicity.nativeMatrix_det_ne_zero E P hP) (Multiplicity.nativeMatrix_hermitian E P hP)
    e (fun x y => (he x y).trans (Multiplicity.native_tensor_trace E P v x y).symm)

theorem nativeLocalCoordinateMatrix_integral_bound :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], N < q →
      ∀ [Algebra E ℚ_[q]] [IsScalarTower ℚ E ℚ_[q]]
        (σ : Fin s → E →ₐ[ℚ] ℚ_[q])
        (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σ)) (i j),
        ‖(nativeLocalCoordinateMatrix E P hP v e he ℚ_[q] σ hσ).val i j‖ ≤ 1 := by
  exact LocalCoordinateIntegral.localSymplecticChange_integral_above_bound E
    (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v)
    (nativeTraceCoefficient_ne_zero E P hP v) (nativeTraceCoefficient_conjugate E P hP v)
    (Multiplicity.nativeMatrix E P) (Multiplicity.nativeMatrix_det_ne_zero E P hP) (Multiplicity.nativeMatrix_hermitian E P hP)
    e (fun x y => (he x y).trans (Multiplicity.native_tensor_trace E P v x y).symm)

theorem nativeLocalCoordinateMatrix_unitary
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
    (σ : Fin s → E →ₐ[ℚ] K) (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Sum (Fin s × Fin 3) (Fin s × Fin 3) → K) :
    (nativeLocalCoordinateMatrix E P hP v e he K σ hσ).val *ᵥ
      ((RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E P e g).map (algebraMap ℚ K) *ᵥ x) =
        LocalUnitaryPhase.Intrinsic.localUnitaryPhase E P K σ g ((nativeLocalCoordinateMatrix E P hP v e he K σ hσ).val *ᵥ x) := by
  unfold nativeLocalCoordinateMatrix
  rw [RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange_mulVec, RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange_mulVec]
  exact LocalUnitaryPhase.Intrinsic.rationalToSplitCoordinates_unitary E P K σ hσ _
    (nativeTraceCoefficient_ne_zero E P hP v) (Multiplicity.nativeMatrix_det_ne_zero E P hP) e g x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalCoordinates
