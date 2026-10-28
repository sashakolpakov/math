import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GoodPrimeTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFixed
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTestNonzero

/-! # Canonical Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalTest.Intrinsic

noncomputable section

section

/-! The data fixed before the prime yields the same spherical test for the actual principal native datum. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E D.pel.reference hg.reference_admissible hμ v hv D.weil)

local notation "e" => R.coordinates
local notation "he" => R.pairing
local notation "T" => R.thetaTest

theorem native_retained_spherical_test
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (hn : 0 < n)
    (hlevel : 0 < D.pel.level) (hdepth : R.depth ∣ D.pel.level)
    (hlarge : max 2 (max R.thetaTest.level
      (Intrinsic.FiniteCoordinates.nativeCoordinateBound E D.pel.reference hg.reference_admissible v e he)) < q) :
    ∃ u : MpF,
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
        (Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) ∧
      ∃ hu : Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u,
        let := Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
        R.thetaTest.test ∈ (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu
          (Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel)).sphericalInputs ∧
        ∃ a : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), a ≠ 0 ∧
          ∃ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
            AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u a b = R.thetaTest.test := by
  obtain ⟨u, huS, hu, hactive, hradial⟩ := GoodPrimeTest.Intrinsic.native_retained_test_at_good_prime hLocalWeil E D hg hq
    hμ v hv e he c hn T hlarge
  refine ⟨u, huS, hu, ?_⟩
  dsimp only
  let := Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let L := Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
  have haway := Intrinsic.AwayFixed.native_retained_principal_away_fixed E D hg hq hμ v hv e he c u hu
    T R.calibration huS hlevel (AdmissibleAwayLevel.Approximation.admissible_lattice_fg E D.pel.reference hg.reference_admissible)
    (AdmissibleAwayLevel.Approximation.admissible_lattice_span E D.pel.reference hg.reference_admissible)
    (R.projective_dvd.trans hdepth) (R.source_depth D.pel.level hdepth) hactive
  exact ⟨Intrinsic.SphericalTest.native_spherical_mem E D hg hμ v hv e he c u hu R.thetaTest.test hactive L haway, hradial⟩

end

/-! The same normalized pre-prime test belongs to the actual principal
spherical space and survives every canonical algebraic theta lift. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hμ : D.pel.reference.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E D.pel.reference hg.reference_admissible hμ v hv D.weil)

theorem native_retained_canonical_test
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (hn : 0 < n)
    (hlevel : 0 < D.pel.level) (hdepth : R.depth ∣ D.pel.level)
    (hlarge : max 2 (max R.thetaTest.level
      (Intrinsic.FiniteCoordinates.nativeCoordinateBound E D.pel.reference hg.reference_admissible v R.coordinates R.pairing)) < q) :
    ∃ u : MpF,
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
        (Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v R.coordinates R.pairing) ∧
      ∃ hu : Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D R.coordinates u,
        let := Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
          (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
        let L := Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
          (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
        let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv R.coordinates R.pairing c u hu L
        ∃ hf : R.thetaTest.test ∈ N.sphericalInputs,
          (∀ (i : Fin D.pel.componentCount)
            (m : N.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
            (Θ : N.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA),
            N.IsCanonicalThetaLift hg i m Θ → Θ ⟨R.thetaTest.test, hf⟩ ≠ 0) ∧
          ∃ a : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), a ≠ 0 ∧
            ∃ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
              AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u a b =
                R.thetaTest.test := by
  obtain ⟨u, hproject, hu, hf, hradial⟩ :=
    native_retained_spherical_test E D hg hq hμ v hv R hLocalWeil c hn hlevel hdepth hlarge
  refine ⟨u, hproject, hu, ?_⟩
  dsimp only
  let := Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
    (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let L := Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
    (Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
  refine ⟨hf, ?_, hradial⟩
  intro i m Θ hΘ
  exact Intrinsic.ThetaTestNonzero.nativeThetaTest_lift_ne_zero E D hg hμ v hv R.coordinates R.pairing c u hu L
    R.thetaTest hf i m Θ hΘ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalTest.Intrinsic
