import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Period
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodMatrixFamilies
import OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity
import OAI.RepresentationTheory.Hecke.RadialDilation.CoordinateTheta

/-! # Period Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodFamily.Multiplicity

noncomputable section

/-! Construct the actual signed native period as a holomorphic family
of Siegel matrices from its PEL trace form. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

include hμ hv he in
theorem native_frame_matrix_conditions (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    (Multiplicity.Period.nativeUpperFrame E P hP v e z).transpose * Multiplicity.Period.nativeLowerFrame E P hP v e z =
      (Multiplicity.Period.nativeLowerFrame E P hP v e z).transpose * Multiplicity.Period.nativeUpperFrame E P hP v e z ∧
    ∀ w : Fin s × Fin 3 → ℂ, w ≠ 0 →
      0 < (RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.standardFramePairing (Multiplicity.Period.nativeUpperFrame E P hP v e z *ᵥ w)
        (Multiplicity.Period.nativeLowerFrame E P hP v e z *ᵥ w)).im := by
  let δ := P.imaginaryScalar
  let t := Multiplicity.nativeCoefficient E P v
  let H := Multiplicity.nativeMatrix E P
  let B := Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings H
  let ec := RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e
  let ψ := Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings H) (fun i => P.embeddings i (δ * t))
  have he' : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) = RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E (δ * t) H x y :=
    fun x y => (he x y).trans (Multiplicity.native_tensor_trace E P v x y).symm
  have hpair : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (ec x) (ec y) = ψ x y :=
    RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.rationalCoordinates_preserves_pairing E P.embeddings hP.1 δ t hP.2.2.2.2.2.2.2.1
      (Multiplicity.nativeCoefficient_real E P hP v) H (Multiplicity.nativeMatrix_hermitian E P hP) e he'
  have hq : B P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
    rw [Multiplicity.Period.native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  have hp : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card (Fin s)) ψ Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame B P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z)) := by
    have hp' := Geometry.ComplexBall.PrescribedSignsB.globalFrame_positivePeriod B (Geometry.ComplexBall.PrescribedSignsB.matrixB_hermitian P.embeddings H (Multiplicity.nativeMatrix_hermitian E P hP))
      P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z hq (fun i => P.embeddings i (δ * t))
      (fun i => Geometry.ComplexBall.PrescribedSignsB.coefficient_real_zero (P.embeddings i) δ t hP.2.2.2.2.2.2.2.1
        (Multiplicity.nativeCoefficient_real E P hP v)) (Multiplicity.Period.native_frame_positive E P hP hμ v hv z hz)
    simpa only [B, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, ψ] using hp'
  exact RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.positivePeriod_frame_matrices ec B P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z ψ hpair
    (RepresentationTheory.Hecke.RadialDilation.RealStructure.Realization.rationalCoordinates_realConj E P.embeddings hP.1 e) hp

include hμ hv he in
theorem native_lowerFrame_det (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    (Multiplicity.Period.nativeLowerFrame E P hP v e z).det ≠ 0 :=
  RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.positive_frame_lower_det _ _ (native_frame_matrix_conditions E P hP hμ v hv e he z hz).2

def nativePeriodMatrix (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : Matrix (Fin s × Fin 3) (Fin s × Fin 3) ℂ :=
  Multiplicity.Period.nativeUpperFrame E P hP v e z * (Multiplicity.Period.nativeLowerFrame E P hP v e z)⁻¹

def nativePeriod (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin s × Fin 3) :=
  RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.siegelOfPositiveFrame (Multiplicity.Period.nativeUpperFrame E P hP v e z) (Multiplicity.Period.nativeLowerFrame E P hP v e z)
    (native_frame_matrix_conditions E P hP hμ v hv e he z z.property).1
    (native_frame_matrix_conditions E P hP hμ v hv e he z z.property).2

theorem nativePeriod_matrix (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (nativePeriod E P hP hμ v hv e he z).matrix = nativePeriodMatrix E P hP v e z := rfl

theorem nativePeriod_columns (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (nativePeriod E P hP hμ v hv e he z).matrix * Multiplicity.Period.nativeLowerFrame E P hP v e z =
      Multiplicity.Period.nativeUpperFrame E P hP v e z :=
  RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization.siegelOfPositiveFrame_columns _ _ _ _

theorem nativePeriod_unique (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain})
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin s × Fin 3))
    (hZ : Z.matrix * Multiplicity.Period.nativeLowerFrame E P hP v e z = Multiplicity.Period.nativeUpperFrame E P hP v e z) :
    Z = nativePeriod E P hP hμ v hv e he z := by
  apply RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.siegel_matrix_ext
  have h := congrArg (fun A : Matrix (Fin s × Fin 3) (Fin s × Fin 3) ℂ =>
    A * (Multiplicity.Period.nativeLowerFrame E P hP v e z)⁻¹) hZ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (native_lowerFrame_det E P hP hμ v hv e he z z.property)),
    Matrix.mul_one] at h
  exact h

include hμ hv he in
theorem nativePeriodMatrix_differentiable :
    DifferentiableOn ℂ (nativePeriodMatrix E P hP v e) P.domain := by
  have hq : ∀ z ∈ P.domain,
      Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
    intro z _
    rw [Multiplicity.Period.native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  exact PeriodMatrixFamilies.Multiplicity.frame_graph_differentiable
    (PeriodFrameFamilies.Multiplicity.upperFrame_differentiable _ _ _ _ _ hq) (PeriodFrameFamilies.Multiplicity.lowerFrame_differentiable _ _ _ _ _ hq)
    (native_lowerFrame_det E P hP hμ v hv e he)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodFamily.Multiplicity
