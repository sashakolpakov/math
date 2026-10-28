import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.SourceActiveLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PELLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayDensity

/-! # Source Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceLevel

noncomputable section

/-! The actual principal native away level and an auxiliary active open
subgroup put a rational element in the same retained AdelicTheta source level. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.SourceActiveLevel.Approximation

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
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem native_source_level_mem
    (hlevel : 0 < D.pel.level)
    (K₀ : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteSU E D.pel.reference hg.reference_admissible))
    (hK₀ : ∀ g : CM.FiniteAway.Approximation.CMFiniteSU E D.pel.reference hg.reference_admissible,
      CM.AwayPELLevel.Approximation.cmOriginalPELHomeomorph E D.pel.reference hg.reference_admissible g ∈
        D.pel.reference.adelicPrincipalLevel D.pel.level → g ∈ K₀)
    (γ : D.RationalSU) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ ∈
      PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel →
    LocalSymplectic.nativeLocalUnitaryBlocks E D γ D.pel.reference.distinguished ∈
      CM.SourceActiveLevel.Approximation.cmSourceActiveLevel E D.pel.reference hg.reference_admissible
        (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)) K₀ D.localLevel.val →
    CM.FiniteAway.Approximation.cmRationalFiniteSU E D.pel.reference hg.reference_admissible γ ∈ K₀ := by
  dsimp only
  intro ha hg₀
  apply CM.SourceActiveLevel.Approximation.cmSourceActiveLevel_rational_mem E D.pel.reference hg.reference_admissible
    (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)) K₀ D.localLevel.val γ hg₀
  apply hK₀
  exact (PELLevel.nativePELLevel_rational E D hg hμ v hv e he c u hu
    (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel γ).mp ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceLevel
