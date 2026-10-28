import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalScalar
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveAway
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators

/-! # Calibrated Away -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CalibratedAway

noncomputable section

/-! Rational scalar calibration removes the same test's away-level character by density. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators.Local OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed.TestTransport

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem native_principal_away_fixed_of_calibration
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (hlevel : 0 < D.pel.level)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (hφ : φ ≠ 0)
    (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (M : ℕ) (hM : 0 < M)
    (hperiod : ∀ z ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (M : ℚ) (by exact_mod_cast hM.ne'), ∀ x, φ.val (z + x) = φ.val x)
    (hfg : D.pel.reference.lattice.FG)
    (hspan : Submodule.span ℚ (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (hdiv : PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth E D.pel.reference e D.weil φ hfg hspan hφ hsupport M hM hperiod ∣
      D.pel.level)
    (K₀ : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteSU E D.pel.reference hg.reference_admissible))
    (hK₀ : ∀ g : CM.FiniteAway.Approximation.CMFiniteSU E D.pel.reference hg.reference_admissible,
      CM.AwayPELLevel.Approximation.cmOriginalPELHomeomorph E D.pel.reference hg.reference_admissible g ∈
        D.pel.reference.adelicPrincipalLevel D.pel.level → g ∈ K₀)
    (hactive : φ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
      (CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u))
    (hcalibration : ∀ γ : D.RationalSU,
      CM.FiniteAway.Approximation.cmRationalFiniteSU E D.pel.reference hg.reference_admissible γ ∈ K₀ → ∀ a : ℂ,
      D.weil.finite.action (RationalSplitting.nativeRationalFiniteSplitting E D.pel.reference
        hg.reference_admissible hμ v hv e he D.weil γ) φ = a • φ → a = 1) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    ∀ a ∈ PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel,
      D.weil.finite.action a.val φ = φ := by
  dsimp only
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let L := PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
  let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L
  let σ := LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)
  let U := CM.SourceActiveLevel.Approximation.cmSourceActiveLevel E D.pel.reference hg.reference_admissible σ K₀ D.localLevel.val
  have hline := ProjectiveAway.native_principal_away_preserves_line E D hg hq hμ v hv e he c u hu huS hlevel
    φ hfg hspan hφ
    hsupport M hM hperiod hdiv
  dsimp only at hline
  apply DenseAwayFixed.TestTransport.dense_away_level_fixed N.rationalFinite
    (UnitaryAwayDensity.native_unitary_away_density E D hg hμ v hv e he c u hu L)
    (AwayRationalEquiv.nativeAwayRationalEquiv E D hg hμ v hv e he c u hu).surjective
    (Commutators.Local.sl3_commutator_eq_top (K := Padic q)) L
    (D.weil.finite.action.comp (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu).range.subtype)
    φ hφ hline U
  intro γ ha hU
  have hi := RestrictedInsert.Approximation.restrictedActiveLevel_le _ (CM.ActivePlace.Approximation.cmActivePlace E σ) K₀ D.localLevel.val
    (CM.SourceActiveLevel.Approximation.cmOriginalActiveInverse E D.pel.reference hg.reference_admissible σ) hU
  change LocalSymplectic.nativeLocalUnitaryBlocks E D γ D.pel.reference.distinguished ∈ D.localLevel.val.toSubgroup at hi
  rw [D.localLevel.property] at hi
  have hmem := SourceLevel.native_source_level_mem E D hg hμ v hv e he c u hu hlevel K₀ hK₀ γ ha hU
  obtain ⟨a, haScalar⟩ := hline (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ) ha
  have hr := RationalScalar.native_rational_action_scalar E D hg hμ v hv e he c u hu φ hactive γ hi a haScalar
  have haOne := hcalibration γ hmem a hr
  change D.weil.finite.action (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ) φ = φ
  exact haScalar.trans (by rw [haOne, one_smul])

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CalibratedAway
