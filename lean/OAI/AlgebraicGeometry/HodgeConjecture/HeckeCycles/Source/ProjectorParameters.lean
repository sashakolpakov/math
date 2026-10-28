import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaClassRelations
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaCanonicalAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ParameterValuations
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryBettiHecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedRadial

/-! # Projector Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectorParameters.CM

noncomputable section

/-! A nonzero projector on an original source theta class selects an
actual auxiliary radial family. Its constructed dilation determines the
parameter and Galois valuations of that same full Hecke character. The
active and away coordinate identities remain explicit intermediate
matrix premises to be discharged by the source splitting construction. -/

open scoped Classical TensorProduct _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates.Local
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hperiod : D.period = L.period) (hproject : D.project = Theta.Projection.CM.projection E L)
  (hdom : B.domainOpen = D.domain)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
  (hd : ∀ τ, d τ = v.val τ⁻¹)

include hperiod hproject hdom hv hd in
theorem parameter_from_family
    (j : CMExtraction.ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (u : MpF)
    (hfamily : ∀ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ) (ω ζ : CMExtraction.ParameterChoices.Qbar),
        0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
        ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
          (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
        (∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1) ∧
        (∀ e₀ : CMExtraction.ParameterChoices.Qbar, e₀ ^ M = ω → ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ e₀)‖ = 1) ∧
        (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
          ScalarFamily.CM.Family.family E L
            (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
          j ω • ScalarFamily.CM.Family.family E L
            (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)))
    {n : ℕ} (c : (GeometricSource.CM.Positions E places) ≃ Fin n)
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (haway : ∀ g ∈ D.awayLevel, ∀ p t : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.weil.finite.project (u * D.splitting (1, g) * u⁻¹)).val.mulVec
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t))
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1))
    (hP : ∀ h, Commute P ((W.action.cohomologyAction h).baseChange ℂ))
    (hspace : LinearMap.range P ≤ HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
      (fun h => j (χ h)))
    (f : D.sphericalInputs) (hne : P (Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W f) ≠ 0) :
    let Ψ := CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) χ
    ∃ a : CMExtraction.ParameterChoices.Qbarˣ,
      (∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ (a : CMExtraction.ParameterChoices.Qbar))‖ = 1) ∧
      HeckeCharacters.CM.Projectors.jointSpace (CMExtraction.Intrinsic.CentralFinite.nativeFullHeckeActionOver D.pel CMExtraction.ParameterChoices.Qbar W.action) Ψ ≠ ⊥ ∧
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D.pel CMExtraction.ParameterChoices.Qbar W.action Ψ)
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) (a : CMExtraction.ParameterChoices.Qbar)) ∧
      ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ),
        let Q := CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D.pel CMExtraction.ParameterChoices.Qbar W.action
          (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) Ψ σ)
        (∃ z : CMExtraction.ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual Q (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) ∧
        ∀ z : CMExtraction.ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual Q (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
          NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) z =
            (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2) := by
  obtain ⟨φ, J, b, hφ, hJ, hneJ⟩ := CMExtraction.Intrinsic.SphericalCoordinates.native_nonzero_spherical_radial_family D c u hp haway
    (P.comp (Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W)) f hne
  obtain ⟨r, M, ω, ζ, hM, hr, hsplit, hζ, hrel, hnorm, _hroot, hsource⟩ := hfamily φ hφ
  let ΘB := (Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W).comp J
  have hδ : ∀ b, ΘB ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • ΘB b := by
    intro b
    exact ThetaClassRelations.CM.dilation E L D hperiod hproject hdom hg hq hIsogenyQuotient W
      J (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) (j ω) (by intro b; rw [hJ, hJ]; exact hsource b) b
  have ht := CMExtraction.Intrinsic.AuxiliaryBettiHecke.native_auxiliary_theta_class_hecke D hg W.action
    (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) W.theta
    (Geometric.ThetaCanonicalAction.CM.covariance D hg hq hIsogenyQuotient W) c u hp φ J hJ hElementaryDivisors
  obtain ⟨a, ha, hna, hocc, hproj⟩ := CMExtraction.ProjectedRadial.Intrinsic.native_full_projected_dual_radial_parameter D hg hq hIsogenyQuotient
    W.action W.realization hElementaryDivisors ΘB M hM j ω hnorm hδ ht χ P hP hspace b hneJ
  refine ⟨a, hna, hocc, hproj, ?_⟩
  have hrel' : ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) := by simpa only [hd] using hrel
  exact ParameterValuations.CM.valuations E places D.pel ιE v hv r M hM hr hsplit ω ζ hζ hrel'
    j hnorm a ha W.action
    (CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) χ)
    (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) hproj

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectorParameters.CM
