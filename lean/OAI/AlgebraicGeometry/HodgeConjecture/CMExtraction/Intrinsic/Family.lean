import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters

/-! # Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Family

noncomputable section

/-! Lift the whole-family dilation through the fixed algebraic embedding,
retaining its scalar, power and exact splitting. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_family_algebraic_dilation_with_local_action
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (j : ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ)) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    ∃ (r : Eˣ) (M : ℕ)
      (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF) (ω ζ : ParameterChoices.Qbar),
      0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
        (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
          if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
      (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.pel.reference,
        (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1) ∧
      (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
        FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
          (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q D.pel.reference.distinguished D.weil u ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
        j ω • FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
          (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q D.pel.reference.distinguished D.weil u b)) ∧
      FiniteDilation.NativeFiniteCoordinateIdentity E D e u := by
  obtain ⟨r, M, e, he, u, hM, hr, hsplit, ⟨ωc, ζc, hζc, htheta, hrel, hωc, _⟩, hlocal⟩ :=
    FamilyDilation.native_family_dilation_with_local_action E hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy D hg hq hμ ιE v hv
  obtain ⟨ω, ζ, hωj, _, hζ, hω, hnorm⟩ := Parameters.ParameterChoices.lift_dilation_parameters E j ιE hι
    (Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (-1)
    ωc ζc hζc hωc (by simpa only [neg_one_mul] using hrel)
  refine ⟨r, M, e, he, u, ω, ζ, hM, hr, hsplit, hζ, ?_, hnorm, ?_, hlocal⟩
  · simpa only [neg_one_mul] using hω
  · simpa only [hωj] using htheta

theorem native_family_algebraic_dilation
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (j : ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ)) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    ∃ (r : Eˣ) (M : ℕ)
      (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF) (ω ζ : ParameterChoices.Qbar),
      0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
        (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
          if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
      (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.pel.reference,
        (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1) ∧
      (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
        FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
          (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q D.pel.reference.distinguished D.weil u ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
        j ω • FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
          (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q D.pel.reference.distinguished D.weil u b)) := by
  obtain ⟨r, M, e, he, u, ω, ζ, hM, hr, hsplit, hζ, hω, hnorm, htheta, _⟩ :=
    native_family_algebraic_dilation_with_local_action E hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy
      D hg hq hμ j ιE hι v hv
  exact ⟨r, M, e, he, u, ω, ζ, hM, hr, hsplit, hζ, hω, hnorm, htheta⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Family
