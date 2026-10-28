import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel

/-! # Cotangent Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentClass

noncomputable section

/-! Relations of the constructed signed frame theta family pass to the
unique GeometricTheta algebraic lift and its actual integration-defined Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
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

theorem nativeCotangentTheta_frame_relation
    (φ ψ : D.sphericalInputs) (ω : ℂ)
    (hrel : FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he φ.val =
      ω • FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he ψ.val) :
    ∀ x : D.domain,
      (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).thetaUniversal φ.val x.val =
        ω • (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).thetaUniversal ψ.val x.val := by
  intro x
  have hx : x.val ∈ D.pel.reference.domain := by
    rw [PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
    exact x.property
  let z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ D.pel.reference.domain} := ⟨x.val, hx⟩
  have h := congrFun hrel z
  rw [CotangentCovariance.withNativeCotangentTheta_coordinates E D hg hμ v hv e he φ.val z,
    CotangentCovariance.withNativeCotangentTheta_coordinates E D hg hμ v hv e he ψ.val z]
  rw [(congrArg FrameProjection.Multiplicity.coordinateCovector h).trans (FrameProjection.Multiplicity.coordinateCovector.map_smul ω _)]
  exact smul_comm _ _ _

theorem nativeCotangentTheta_frame_class_relation
    (j : Fin D.pel.componentCount) (c : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg j c Θ)
    (hu : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg j c Ψ → Ψ = Θ)
    (φ ψ : D.sphericalInputs) (ω : ℂ)
    (hrel : FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he φ.val =
      ω • FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he ψ.val) :
    ThetaClass.nativeThetaClass D hg Θ φ = ω • ThetaClass.nativeThetaClass D hg Θ ψ :=
  ThetaLiftKernel.Intrinsic.canonicalTheta_class_relation (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he) hg j c Θ hΘ hu φ ψ ω
    (nativeCotangentTheta_frame_relation E D hg hμ v hv e he φ ψ ω hrel)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentClass
