import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodPairing
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HodgeEquivalenceInverse

/-! # Intrinsic Period Hodge -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodHodge

noncomputable section

/-! The polarization pairing gives a genuine Hodge realization of the
native period kernel by the same abelian variety's canonical H1. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

private theorem covector_factors_through_surjection
    {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (p : U →ₗ[ℂ] V) (hp : Function.Surjective p) (q : U →ₗ[ℂ] ℂ)
    (hker : p.ker ≤ q.ker) : ∃ f : V →ₗ[ℂ] ℂ, ∀ u, f (p u) = q u := by
  let f := (p.ker.liftQ q hker).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  refine ⟨f, fun u => ?_⟩
  simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A))

theorem nativePeriodH1Equiv_isHodgeMap :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (ArithmeticGeometry.Descent.CMVariety.Canonical.Abelian.IntrinsicPeriods.canonicalH1 A)
      (IntrinsicPeriodPairing.nativePeriodH1Equiv A P).toLinearMap := by
  intro u hu
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1
    ((IntrinsicPeriodPairing.nativePeriodH1Equiv A P).toLinearMap.baseChange ℂ u) ∈ A.variety.pureBettiSubspace 1 0
  apply (HodgeConjecture.DegreeTwo.Periods.Constructions.HodgePeriods.holomorphic_iff_complexLinear_periods ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A _).mpr
  obtain ⟨f, hf⟩ := covector_factors_through_surjection (AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A)
    (AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_surjective A) ((P.form.baseChange ℂ) u)
    (fun v hv => P.holomorphic_isotropic u hu v hv)
  refine ⟨f, fun ℓ => ?_⟩
  rw [IntrinsicPeriodPairing.nativePeriodH1Equiv_complex_period, ← hf]
  change f ((1 : ℂ) • (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = f (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
  rw [one_smul]

theorem nativePeriodH1Equiv_symm_isHodgeMap :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (ArithmeticGeometry.Descent.CMVariety.Canonical.Abelian.IntrinsicPeriods.canonicalH1 A) (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A)
      (IntrinsicPeriodPairing.nativePeriodH1Equiv A P).symm.toLinearMap :=
  HodgeEquivalenceInverse.inverse_isHodgeMap_of_equiv _ _ _ (nativePeriodH1Equiv_isHodgeMap A P)

def nativePeriodH1Realization : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) where
  abelianVariety := A
  comparison := IntrinsicPeriodPairing.nativePeriodH1Equiv A P
  holomorphic x := by
    change (IntrinsicPeriodPairing.nativePeriodH1Equiv A P).toLinearMap.baseChange ℂ x ∈
      (ArithmeticGeometry.Descent.CMVariety.Canonical.Abelian.IntrinsicPeriods.canonicalH1 A).holomorphic ↔ x ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).holomorphic
    constructor
    · intro hx
      have h := nativePeriodH1Equiv_symm_isHodgeMap A P _ hx
      change ((IntrinsicPeriodPairing.nativePeriodH1Equiv A P).baseChange ℚ ℂ _ _).symm
        ((IntrinsicPeriodPairing.nativePeriodH1Equiv A P).baseChange ℚ ℂ _ _ x) ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).holomorphic at h
      simpa only [LinearEquiv.symm_apply_apply] using h
    · exact nativePeriodH1Equiv_isHodgeMap A P x
  antiholomorphic x := by
    change (IntrinsicPeriodPairing.nativePeriodH1Equiv A P).toLinearMap.baseChange ℂ x ∈
      (ArithmeticGeometry.Descent.CMVariety.Canonical.Abelian.IntrinsicPeriods.canonicalH1 A).antiholomorphic ↔ x ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).antiholomorphic
    constructor
    · intro hx
      have h := (nativePeriodH1Equiv_symm_isHodgeMap A P).map_antiholomorphic hx
      change ((IntrinsicPeriodPairing.nativePeriodH1Equiv A P).baseChange ℚ ℂ _ _).symm
        ((IntrinsicPeriodPairing.nativePeriodH1Equiv A P).baseChange ℚ ℂ _ _ x) ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A).antiholomorphic at h
      simpa only [LinearEquiv.symm_apply_apply] using h
    · exact (nativePeriodH1Equiv_isHodgeMap A P).map_antiholomorphic

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodHodge
