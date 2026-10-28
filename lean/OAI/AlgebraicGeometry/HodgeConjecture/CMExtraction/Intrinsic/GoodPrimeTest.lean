import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralTest

/-! # Good Prime Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.GoodPrimeTest

noncomputable section

/-! For every sufficiently large good split prime, the test chosen
before that prime is fixed by the actual native local action and belongs
to one of its actual nonzero auxiliary radial families. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest.Multiplicity OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralTest.Local

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

def nativeThetaTestBound
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y)) : ℕ :=
  max 2 (max (NonzeroTest.nativeThetaTest E P hP hμ v hv e he).level (FiniteCoordinates.nativeCoordinateBound E P hP v e he))

theorem native_nonzero_test_at_good_prime
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (hn : 0 < n)
    (hlarge : nativeThetaTestBound E D.pel.reference hg.reference_admissible hμ v hv e he < q) :
    let T := NonzeroTest.nativeThetaTest E D.pel.reference hg.reference_admissible hμ v hv e he
    ∃ u : MpF,
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
        (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) ∧
      FiniteDilation.NativeFiniteCoordinateIdentity E D e u ∧
      T.test ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
        (CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u) ∧
      ∃ a : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), a ≠ 0 ∧
        ∃ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
          AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u a b = T.test := by
  dsimp only
  let T := NonzeroTest.nativeThetaTest E D.pel.reference hg.reference_admissible hμ v hv e he
  let B := FiniteCoordinates.nativeCoordinateBound E D.pel.reference hg.reference_admissible v e he
  have hlarge' : max 2 (max T.level B) < q := hlarge
  have htwo : 2 < q := lt_of_le_of_lt (le_max_left _ _) hlarge'
  have hlevel : T.level < q :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlarge'
  have hcoord : B < q :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlarge'
  have hcop : q.Coprime T.level := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt T.level_pos hlevel)
  obtain ⟨u, hu, hlocal⟩ := FiniteCoordinates.exists_native_fixed_finite_coordinates E D hg hq v e he
  have hS := FiniteCoordinates.nativeFiniteCoordinateMatrix_integral E D hg hq v e he hcoord
  refine ⟨u, hu, hlocal, ?_, ?_⟩
  · exact IntegralTest.Local.integral_coordinate_dual_fixed q c D.pel.reference.distinguished hLocalWeil hn htwo D.weil
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) u hu hS
      T.test T.support T.level T.level_pos hcop T.period
  · exact IntegralTest.Local.integral_coordinate_radial_preimage q c D.pel.reference.distinguished hLocalWeil hn htwo D.weil
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) u hu hS
      T.test T.support T.level T.level_pos hcop T.period
      (NonzeroTest.nativeThetaTest_ne_zero E D.pel.reference hg.reference_admissible hμ v hv e he T)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.GoodPrimeTest
