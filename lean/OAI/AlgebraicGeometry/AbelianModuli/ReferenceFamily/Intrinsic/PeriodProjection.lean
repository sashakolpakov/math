import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Period Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

noncomputable section

/-! Complexifying the actual rational period inclusion gives a
surjective projection to the native tangent space, with explicit
coordinates supplied by the genuine integral period basis. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

def complexPeriodProjection : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype.liftBaseChange ℂ

theorem complexPeriodProjection_tmul (z : ℂ) (u : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    complexPeriodProjection A (z ⊗ₜ[ℚ] u) = z • u.val := rfl

def complexPeriodBasis := (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A).baseChange ℂ

theorem complexPeriodBasis_apply (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    complexPeriodBasis A i = 1 ⊗ₜ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i :=
  Module.Basis.baseChange_apply ℂ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A) i

theorem realPeriodBasis_eq_rational (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i = (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val := by
  let : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Torsion.IntrinsicTorsion.e06Input A
  exact (Module.Basis.ofZLatticeBasis_apply ℝ _ (Torsion.IntrinsicTorsion.periodBasis A) i).trans
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i).symm

theorem complexPeriodProjection_basis (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    complexPeriodProjection A (complexPeriodBasis A i) = RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i := by
  rw [complexPeriodBasis_apply, complexPeriodProjection_tmul, one_smul,
    realPeriodBasis_eq_rational]

theorem complexPeriodProjection_expansion (u : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    complexPeriodProjection A u =
      ∑ i, (complexPeriodBasis A).repr u i • RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i := by
  have h := congrArg (complexPeriodProjection A) ((complexPeriodBasis A).sum_repr u)
  simpa only [map_sum, map_smul, complexPeriodProjection_basis] using h.symm

theorem complexPeriodProjection_surjective : Function.Surjective (complexPeriodProjection A) := by
  intro v
  refine ⟨∑ i, ((RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr v i : ℂ) • complexPeriodBasis A i, ?_⟩
  rw [map_sum]
  have he : (∑ i, complexPeriodProjection A
      (((RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr v i : ℂ) • complexPeriodBasis A i)) =
      ∑ i, (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr v i • RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, complexPeriodProjection_basis]
    exact Complex.coe_smul _ _
  exact he.trans ((RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).sum_repr v)

theorem complexPeriodProjection_ker_finrank :
    Module.finrank ℂ (complexPeriodProjection A).ker =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
  have hdim := (complexPeriodProjection A).finrank_range_add_finrank_ker
  have hs := LinearMap.range_eq_top.mpr (complexPeriodProjection_surjective A)
  have hsource : Module.finrank ℂ (ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) =
      2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
    rw [Module.finrank_eq_card_basis (complexPeriodBasis A), Fintype.card_fin]
  have htarget : Module.finrank ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := Module.finrank_fin_fun ℂ
  rw [hs, finrank_top, hsource, htarget] at hdim
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods
