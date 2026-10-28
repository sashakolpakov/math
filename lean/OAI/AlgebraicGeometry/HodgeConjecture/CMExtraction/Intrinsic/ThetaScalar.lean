import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Period
import OAI.RepresentationTheory.Hecke.RadialDilation.CoordinateTheta

/-! # Theta Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaScalar

noncomputable section

/-! The actual signed native period supplies the determinant character and
the projected first-theta covariance in the same rational coordinates as
the finite scalar. Positivity and determinant identities are conclusions. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.CoordinateTheta.Realization OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Period
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_theta_scalar_realization
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar *
        Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ) (hγ : γ.val = RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ D.pel.reference.domain) :
    ∃ Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin s × Fin 3),
      RepresentationTheory.Hecke.RadialDilation.GeometricSpecs.Realization.ThetaScalarRealization (Place := Fin s) (MpR := MpR) (MpF := MpF) (MpA := MpA)
        D.weil γ D.pel.reference.distinguished
        (Multiplicity.Period.nativeCompactSigns E D.pel.reference v)
        (fun i => D.pel.reference.embeddings i (r : E))
        (Multiplicity.Period.nativeUpperFrame E D.pel.reference hg.reference_admissible v e z)
        (Multiplicity.Period.nativeLowerFrame E D.pel.reference hg.reference_admissible v e z) Z := by
  let P := D.pel.reference
  have hP := hg.reference_admissible
  have he' : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeMatrix E P) x y :=
    fun x y => (he x y).trans (Multiplicity.native_tensor_trace E P v x y).symm
  have hq : Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
    rw [Multiplicity.Period.native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  have hresult := RepresentationTheory.Hecke.RadialDilation.CoordinateTheta.Realization.geometric_theta_inputs_for_coordinates
    (Place := Fin s) (MpR := MpR) (MpF := MpF) (MpA := MpA) hPoissonAutomorphy E r hr P.embeddings hP.1
    P.imaginaryScalar (Multiplicity.nativeCoefficient E P v) hP.2.2.2.2.2.2.2.1
    (Multiplicity.nativeCoefficient_real E P hP v) (Multiplicity.nativeMatrix E P) (Multiplicity.nativeMatrix_hermitian E P hP)
    e he' P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z hq
    (Multiplicity.Period.native_frame_positive E P hP hμ v hv z hz) D.weil γ hγ
  obtain ⟨Z, hframe, hdet, htheta⟩ := hresult
  refine ⟨Z, ?_, hdet, ?_⟩
  · exact hframe
  · exact htheta

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaScalar
