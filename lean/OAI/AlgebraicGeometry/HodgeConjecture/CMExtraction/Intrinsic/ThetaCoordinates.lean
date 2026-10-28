import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection

/-! # Theta Coordinates -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaCoordinates.Multiplicity

/-! Construct the signed native theta period and cotangent projection
in the exact GeometricTheta function spaces. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

def nativeThetaPeriod (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin s × Fin 3) :=
  if hz : z ∈ P.domain then PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he ⟨z, hz⟩
  else PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (PeriodDomain.Multiplicity.nativeOrigin E P hP)

theorem nativeThetaPeriod_on_domain (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hz : z ∈ P.domain) :
    nativeThetaPeriod E P hP hμ v hv e he z = PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he ⟨z, hz⟩ := by
  simp only [nativeThetaPeriod, dite_eq_left hz]

theorem nativeThetaPeriod_differentiable :
    DifferentiableOn ℂ (fun z => (nativeThetaPeriod E P hP hμ v hv e he z).matrix) P.domain := by
  apply (PeriodFamily.Multiplicity.nativePeriodMatrix_differentiable E P hP hμ v hv e he).congr
  intro z hz
  rw [nativeThetaPeriod_on_domain E P hP hμ v hv e he z hz]
  rfl

def nativeThetaProjection (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (((Fin s × Fin 3) → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent :=
  FrameProjection.Multiplicity.frameProjection (fun i => (P.distinguished, i.succ)) (Multiplicity.Period.nativeLowerFrame E P hP v e z)

include hμ hv he in
theorem nativeThetaProjection_differentiable :
    DifferentiableOn ℂ (nativeThetaProjection E P hP v e) P.domain := by
  have hq : ∀ z ∈ P.domain,
      Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
    intro z _
    rw [Multiplicity.Period.native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  exact FrameProjection.Multiplicity.frameProjection_differentiable _ _ (PeriodFrameFamilies.Multiplicity.lowerFrame_differentiable _ _ _ _ _ hq)
    (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he)

def nativeThetaOneForm : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3) →ₗ[ℂ] (RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
  RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear (nativeThetaPeriod E P hP hμ v hv e he) (nativeThetaProjection E P hP v e)

theorem nativeThetaOneForm_holomorphic (Φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) :
    DifferentiableOn ℂ (nativeThetaOneForm E P hP hμ v hv e he Φ) P.domain :=
  RepresentationTheory.Theta.Geometric.LinearTheta.canonical_oneForm_holomorphic P.domain _ (nativeThetaPeriod_differentiable E P hP hμ v hv e he)
    _ (nativeThetaProjection_differentiable E P hP hμ v hv e he) Φ

theorem nativeThetaOneForm_coordinates (Φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain}) :
    nativeThetaOneForm E P hP hμ v hv e he Φ z =
      FrameProjection.Multiplicity.coordinateCovector (FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he Φ z) := by
  change FrameProjection.Multiplicity.frameProjection _ _ (RepresentationTheory.Theta.Geometric.LinearTheta.firstThetaLinear (nativeThetaPeriod E P hP hμ v hv e he z) Φ) = _
  rw [nativeThetaPeriod_on_domain E P hP hμ v hv e he z z.property]
  rfl

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaCoordinates.Multiplicity

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaCoordinates

/-! Put the constructed signed period and cotangent projection into the
native GeometricTheta datum. Holomorphicity and the theta identification are derived. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))

def withNativeTheta : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA :=
  { D with
    period := Multiplicity.nativeThetaPeriod E D.pel.reference hg.reference_admissible hμ v hv e he
    project := Multiplicity.nativeThetaProjection E D.pel.reference hg.reference_admissible v e }

theorem withNativeTheta_holomorphic : (withNativeTheta E D hg hμ v hv e he).HasHolomorphicThetaData := by
  change DifferentiableOn ℂ
      (fun z => (Multiplicity.nativeThetaPeriod E D.pel.reference hg.reference_admissible hμ v hv e he z).matrix)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b)) ∧
    DifferentiableOn ℂ (Multiplicity.nativeThetaProjection E D.pel.reference hg.reference_admissible v e)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b))
  rw [← PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
  exact ⟨Multiplicity.nativeThetaPeriod_differentiable E D.pel.reference hg.reference_admissible hμ v hv e he,
    Multiplicity.nativeThetaProjection_differentiable E D.pel.reference hg.reference_admissible hμ v hv e he⟩

theorem withNativeTheta_universal :
    (withNativeTheta E D hg hμ v hv e he).thetaUniversal =
      Multiplicity.nativeThetaOneForm E D.pel.reference hg.reference_admissible hμ v hv e he := rfl

theorem withNativeTheta_finiteCoordinates (hc : D.HasFiniteCoordinates) :
    (withNativeTheta E D hg hμ v hv e he).HasFiniteCoordinates := hc

theorem withNativeTheta_coordinates (Φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ D.pel.reference.domain}) :
    (withNativeTheta E D hg hμ v hv e he).thetaUniversal Φ z =
      FrameProjection.Multiplicity.coordinateCovector (FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he Φ z) :=
  Multiplicity.nativeThetaOneForm_coordinates E D.pel.reference hg.reference_admissible hμ v hv e he Φ z

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaCoordinates

end

end OAI
