import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameThetaAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCotangent

/-! # Cotangent Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance

noncomputable section

section

/-! Rational covariance of the normalized native cotangent theta form.
Both the finite action and the projective differential are the constructed
native maps; no automorphy hypothesis is introduced. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq PeriodAction.Multiplicity.nativeDomainAction

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

omit [IsGalois ℚ E] in
include hP in
theorem native_cotangent_matrix_identity (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) (c u : Fin 2 → ℂ) :
    HalfCocycle.nativeProjectiveFactor E P g x *
        FrameProjection.Multiplicity.coordinateCovector (UnitaryFrameAction.weightedDualCoordinates (P.μ P.b)
          (ArchFrame.archConjugateUnitaryBlock E P P.distinguished g) x *ᵥ c)
          (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g) x.val u) = FrameProjection.Multiplicity.coordinateCovector c u := by
  have hO : IsOpen P.domain := by
    rw [PeriodDomain.Multiplicity.native_domain_eq_ball E P]
    exact (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b)).isOpen
  have hx : x.val ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) := by
    change x.val ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) : Set RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    rw [← PeriodDomain.Multiplicity.native_domain_eq_ball E P]
    exact x.property
  have hf : DifferentiableAt ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g) x.val :=
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_differentiableOn P.b P.μ g x hx).differentiableAt
      ((Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b)).isOpen.mem_nhds hx)
  exact ProjectiveCotangent.Frame.weighted_cotangent (P.μ P.b) ((map_ne_zero P.μ).mpr hP.2.2.1)
    _ _ (ArchFrame.arch_unitary_cross E P P.distinguished g) P.domain hO x x.property
    (ArchFrame.native_arch_denominator_ne_zero E P g) (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g) hf
    (fun y hy => (ArchFrame.native_chartImage_eq_periodMap E P g y hy).symm) c u

variable {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

theorem nativeCotangentTheta_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he
        (D.finite.action (RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he D g) φ)
        (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g x.val)).comp (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g) x.val) =
      CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he φ x.val := by
  change (CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he
    (D.finite.action (RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he D g) φ) (g • x).val).comp _ = _
  rw [CotangentTheta.Multiplicity.nativeCotangentThetaOneForm_coordinates E P hP hμ v hv e he _ (g • x),
    CotangentTheta.Multiplicity.nativeCotangentThetaOneForm_coordinates E P hP hμ v hv e he φ x,
    FrameThetaAction.native_frame_theta_transform E P hP hμ v hv e he D g φ x,
    map_smul FrameProjection.Multiplicity.coordinateCovector (HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x)]
  apply ContinuousLinearMap.ext
  intro u
  let c := FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he φ x
  let L := FrameProjection.Multiplicity.coordinateCovector (UnitaryFrameAction.weightedDualCoordinates (P.μ P.b)
    (ArchFrame.archConjugateUnitaryBlock E P P.distinguished g) x *ᵥ c)
      (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g) x.val u)
  change (FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he (g • x))⁻¹ *
      (HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x * L) =
    (FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he x)⁻¹ * FrameProjection.Multiplicity.coordinateCovector c u
  calc
    _ = (FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he x)⁻¹ * (HalfCocycle.nativeProjectiveFactor E P g x * L) := by
      unfold HalfCocycle.nativeHalfFactor
      field_simp [FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he x,
        FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he (g • x)]
    _ = _ := by rw [native_cotangent_matrix_identity E P hP g x c u]

end

/-! Put the constructed signed period and cotangent projection into the
native GeometricTheta datum. Holomorphicity and the theta identification are derived. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity
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

def withNativeCotangentTheta : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA :=
  { D with
    period := ThetaCoordinates.Multiplicity.nativeThetaPeriod E D.pel.reference hg.reference_admissible hμ v hv e he
    project := CotangentTheta.Multiplicity.nativeCotangentProjection E D.pel.reference hg.reference_admissible hμ v hv e he }

theorem withNativeCotangentTheta_holomorphic : (withNativeCotangentTheta E D hg hμ v hv e he).HasHolomorphicThetaData := by
  change DifferentiableOn ℂ
      (fun z => (ThetaCoordinates.Multiplicity.nativeThetaPeriod E D.pel.reference hg.reference_admissible hμ v hv e he z).matrix)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b)) ∧
    DifferentiableOn ℂ (CotangentTheta.Multiplicity.nativeCotangentProjection E D.pel.reference hg.reference_admissible hμ v hv e he)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b))
  rw [← PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
  exact ⟨ThetaCoordinates.Multiplicity.nativeThetaPeriod_differentiable E D.pel.reference hg.reference_admissible hμ v hv e he,
    CotangentTheta.Multiplicity.nativeCotangentProjection_differentiable E D.pel.reference hg.reference_admissible hμ v hv e he⟩

theorem withNativeCotangentTheta_universal :
    (withNativeCotangentTheta E D hg hμ v hv e he).thetaUniversal =
      CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E D.pel.reference hg.reference_admissible hμ v hv e he := rfl

theorem withNativeCotangentTheta_finiteCoordinates (hc : D.HasFiniteCoordinates) :
    (withNativeCotangentTheta E D hg hμ v hv e he).HasFiniteCoordinates := hc

theorem withNativeCotangentTheta_coordinates (Φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ D.pel.reference.domain}) :
    (withNativeCotangentTheta E D hg hμ v hv e he).thetaUniversal Φ z =
      (FrameRoot.Multiplicity.nativeFrameRoot E D.pel.reference hg.reference_admissible hμ v hv e he z)⁻¹ •
        FrameProjection.Multiplicity.coordinateCovector (FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he Φ z) :=
  CotangentTheta.Multiplicity.nativeCotangentThetaOneForm_coordinates E D.pel.reference hg.reference_admissible hμ v hv e he Φ z

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance
