import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CalibratedAway
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveAway
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators

/-! # Away Fixed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFixed

noncomputable section

/-! Exact principal away fixedness for a retained calibrated theta test. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest.Multiplicity OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators.Local OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed.TestTransport

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

theorem native_retained_principal_away_fixed
    (T : NonzeroTest.NativeThetaTest E D.pel.reference hg.reference_admissible hμ v hv e he)
    (R : RationalTest.Intrinsic.RationalTestCalibration E D.pel.reference hg.reference_admissible hμ v hv e he D.weil T.test)
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (hlevel : 0 < D.pel.level)
    (hfg : D.pel.reference.lattice.FG)
    (hspan : Submodule.span ℚ (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (hdiv : PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth E D.pel.reference e D.weil T.test hfg hspan
      (NonzeroTest.nativeThetaTest_ne_zero E D.pel.reference hg.reference_admissible hμ v hv e he T)
      T.support T.level T.level_pos T.period ∣ D.pel.level)
    (hK : ∀ g : CM.FiniteAway.Approximation.CMFiniteSU E D.pel.reference hg.reference_admissible,
      CM.AwayPELLevel.Approximation.cmOriginalPELHomeomorph E D.pel.reference hg.reference_admissible g ∈
        D.pel.reference.adelicPrincipalLevel D.pel.level → g ∈ R.sourceLevel)
    (hactive : T.test ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
      (CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u)) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    ∀ a ∈ PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel,
      D.weil.finite.action a.val T.test = T.test :=
  CalibratedAway.native_principal_away_fixed_of_calibration E D hg hq hμ v hv e he c u hu huS hlevel
    T.test (NonzeroTest.nativeThetaTest_ne_zero E D.pel.reference hg.reference_admissible hμ v hv e he T)
    T.support T.level T.level_pos T.period hfg hspan hdiv R.sourceLevel hK hactive R.calibrated

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFixed
