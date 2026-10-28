import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryBettiHecke

/-! # Auxiliary Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryClass

noncomputable section

/-! The actual canonical algebraic theta lift transfers the arbitrary
auxiliary family's dilation and its native spherical Hecke action to
the same integration-defined Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open scoped Classical TensorProduct

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

theorem native_auxiliary_theta_class_dilation
    (i : Fin D.pel.componentCount) (c : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg i c Θ)
    (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg i c Ψ → Ψ = Θ)
    (u : MpF) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs)
    (hJ : ∀ b, (J b).val = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (M : ℕ) (ω : ℂ)
    (hframe : ∀ b, FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
      (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
        (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)) :
    ∀ b, ThetaClass.nativeThetaClass D hg Θ (J ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) = ω • ThetaClass.nativeThetaClass D hg Θ (J b) := by
  intro b
  apply CotangentClass.nativeCotangentTheta_frame_class_relation E D hg hμ v hv e he i c Θ hΘ huniq
  rw [hJ, hJ]
  exact hframe b

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryClass
