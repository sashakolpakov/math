import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.GoodPrimeTest

/-! # Good Prime Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GoodPrimeTest.Intrinsic

noncomputable section

/-! The good-prime construction for any retained normalized test in the original coordinates. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem native_retained_test_at_good_prime
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
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (hn : 0 < n)
    (T : Intrinsic.NonzeroTest.NativeThetaTest E D.pel.reference hg.reference_admissible hμ v hv e he)
    (hlarge : max 2 (max T.level (Intrinsic.FiniteCoordinates.nativeCoordinateBound E D.pel.reference hg.reference_admissible v e he)) < q) :
    ∃ u : MpF,
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
        (Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) ∧
      Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u ∧
      T.test ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
        (CoordinateDualHecke.Local.coordinateDualRepresentation q c D.pel.reference.distinguished D.weil u) ∧
      ∃ a : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), a ≠ 0 ∧
        ∃ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
          AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u a b = T.test := by
  let B := Intrinsic.FiniteCoordinates.nativeCoordinateBound E D.pel.reference hg.reference_admissible v e he
  have hlarge' : max 2 (max T.level B) < q := hlarge
  have htwo : 2 < q := lt_of_le_of_lt (le_max_left _ _) hlarge'
  have hlevel : T.level < q :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlarge'
  have hcoord : B < q :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlarge'
  have hcop : q.Coprime T.level := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt T.level_pos hlevel)
  obtain ⟨u, hu, hlocal⟩ := Intrinsic.FiniteCoordinates.exists_native_fixed_finite_coordinates E D hg hq v e he
  have hS := Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix_integral E D hg hq v e he hcoord
  refine ⟨u, hu, hlocal, ?_, ?_⟩
  · exact Intrinsic.IntegralTest.Local.integral_coordinate_dual_fixed q c D.pel.reference.distinguished hLocalWeil hn htwo D.weil
      (Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) u hu hS
      T.test T.support T.level T.level_pos hcop T.period
  · exact Intrinsic.IntegralTest.Local.integral_coordinate_radial_preimage q c D.pel.reference.distinguished hLocalWeil hn htwo D.weil
      (Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) u hu hS
      T.test T.support T.level T.level_pos hcop T.period
      (Intrinsic.NonzeroTest.nativeThetaTest_ne_zero E D.pel.reference hg.reference_admissible hμ v hv e he T)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GoodPrimeTest.Intrinsic
