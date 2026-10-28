import OAI.RepresentationTheory.Hecke.IntrinsicDatum
import OAI.RepresentationTheory.Hecke.CanonicalRelations
import OAI.RepresentationTheory.Hecke.RadialComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Canonical Dilation -/

namespace OAI.RepresentationTheory.Hecke.CanonicalDilation.SphericalActionIntrinsic

noncomputable section

/-! The normalized native cotangent theta form and the GeometricTheta unique
algebraic lift preserve the same whole-family dilation relation. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
  [TopologicalSpace (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

local notation "N" => OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L

theorem canonical_native_dilation
    (j : Fin D.pel.componentCount)
    (cover : (N).domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : (N).sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (N).IsCanonicalThetaLift hg j cover Θ)
    (huniq : ∀ Ψ, (N).IsCanonicalThetaLift hg j cover Ψ → Ψ = Θ)
    (φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : SphericalActionModelInverse.Radial q →ₗ[ℂ] (N).sphericalInputs)
    (hJ : ∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (M : ℕ) (ω : ℂ)
    (hframe : ∀ b, AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ ((RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)) :
    ∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b) := by
  intro b
  apply CanonicalRelations.SphericalActionIntrinsic.canonicalTheta_lift_relation N hg j cover Θ hΘ huniq
  intro x
  let z : {z : Theta.Geometric.LinearTheta.BallCoordinates // z ∈ D.pel.reference.domain} :=
    ⟨x.val, by rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]; exact x.property⟩
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E D.pel.reference hg.reference_admissible hμ v hv e he
      (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)).val z.val =
    ω • AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E D.pel.reference hg.reference_admissible hμ v hv e he (J b).val z.val
  rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm_coordinates, AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm_coordinates, hJ, hJ,
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation.dilationEquiv_pow_apply]
  have h := congrFun (hframe b) z
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ ((RadialDilation.Mem.Realization.dilation q ^ M) b)) z =
    ω • AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) z at h
  rw [h, map_smul, smul_comm]

end

end OAI.RepresentationTheory.Hecke.CanonicalDilation.SphericalActionIntrinsic
