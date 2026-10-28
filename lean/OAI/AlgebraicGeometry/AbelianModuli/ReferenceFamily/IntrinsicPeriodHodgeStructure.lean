import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TypeElevenBilinear
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType

/-! # Intrinsic Period Hodge Structure -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods

noncomputable section

section

/-! The real and imaginary coefficients in the genuine period basis
recover a complexified rational period. Its native projection and the
projection of its conjugate determine it uniquely. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

theorem complexPeriodBasis_repr_conjugation (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) i =
      star ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr u i) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv, star_add]
  | tmul z v =>
      have hl := Module.Basis.baseChange_repr_tmul ℂ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A) (star z) v i
      have hr := Module.Basis.baseChange_repr_tmul ℂ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A) z v i
      have hs := (Complex.conjAe.restrictScalars ℚ).toLinearMap.map_smul
        ((Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A).repr v i) z
      exact hl.trans (hs.symm.trans (congrArg star hr).symm)

def periodRealPart (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  ∑ i, ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr u i).re • Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i

def periodImaginaryPart (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  ∑ i, ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr u i).im • Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i

theorem periodRealPart_conjugation (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    periodRealPart A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) = periodRealPart A u := by
  simp only [periodRealPart, complexPeriodBasis_repr_conjugation, Complex.star_def, Complex.conj_re]

theorem periodImaginaryPart_conjugation (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    periodImaginaryPart A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) = -periodImaginaryPart A u := by
  simp only [periodImaginaryPart, complexPeriodBasis_repr_conjugation, Complex.star_def,
    Complex.conj_im, neg_smul, Finset.sum_neg_distrib]

theorem complexPeriodProjection_real_imaginary (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u = periodRealPart A u + Complex.I • periodImaginaryPart A u := by
  rw [Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_expansion, periodRealPart, periodImaginaryPart,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (TypeElevenBilinear.complex_smul_real_imag _ _).trans
    (congrArg (fun v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A => ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr u i).re • Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i + v)
      (smul_comm _ _ _))

theorem periodRealImaginary_zero (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hr : periodRealPart A u = 0) (hi : periodImaginaryPart A u = 0) : u = 0 := by
  apply (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr.injective
  apply Finsupp.ext
  intro i
  apply Complex.ext
  · have h := congrArg (fun v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A => (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr v i) hr
    change (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr (∑ j, ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr u j).re • Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A j) i = _ at h
    rw [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h
    exact h
  · have h := congrArg (fun v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A => (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr v i) hi
    change (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).repr (∑ j, ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A).repr u j).im • Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A j) i = _ at h
    rw [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h
    exact h

theorem complexPeriodProjection_conjugate_joint_zero (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hu : Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u = 0)
    (hc : Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u) = 0) : u = 0 := by
  have hsum : periodRealPart A u + Complex.I • periodImaginaryPart A u = 0 :=
    (complexPeriodProjection_real_imaginary A u).symm.trans hu
  have hdiff : periodRealPart A u - Complex.I • periodImaginaryPart A u = 0 := by
    have h := (complexPeriodProjection_real_imaginary A
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)).symm.trans hc
    simpa only [periodRealPart_conjugation, periodImaginaryPart_conjugation, smul_neg, sub_eq_add_neg] using h
  have hr : periodRealPart A u = 0 := by
    have ht : (2 : ℂ) • periodRealPart A u = 0 := by
      calc
        (2 : ℂ) • periodRealPart A u =
            (periodRealPart A u + Complex.I • periodImaginaryPart A u) +
              (periodRealPart A u - Complex.I • periodImaginaryPart A u) := by module
        _ = 0 := by rw [hsum, hdiff, add_zero]
    exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
  have hi : periodImaginaryPart A u = 0 := by
    have ht : Complex.I • periodImaginaryPart A u = 0 := by simpa only [hr, zero_add] using hsum
    exact (smul_eq_zero.mp ht).resolve_left Complex.I_ne_zero
  exact periodRealImaginary_zero A u hr hi

end

/-! The kernel of the actual complexified period projection and its
conjugate define complementary native weight-one Hodge subspaces. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

def coefficientConjugationEquiv (U : Type*) [AddCommGroup U] [Module ℚ U] :
    ComplexMultiplication.WeightOne.CM.Complexification U ≃ₗ⋆[ℂ] ComplexMultiplication.WeightOne.CM.Complexification U where
  toFun := ComplexMultiplication.WeightOne.CM.coefficientConjugation U
  invFun := ComplexMultiplication.WeightOne.CM.coefficientConjugation U
  left_inv := ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive U
  right_inv := ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive U
  map_add' := (ComplexMultiplication.WeightOne.CM.coefficientConjugation U).map_add
  map_smul' := ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_smul U

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

def conjugatePeriodKernel : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :=
  (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker.comap (coefficientConjugationEquiv (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)).toLinearMap

def periodKernelConjugation : (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker ≃ₗ⋆[ℂ] conjugatePeriodKernel A where
  toFun u := ⟨ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val, by
    change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val)) = 0
    rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive]
    exact u.property⟩
  invFun u := ⟨ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val, u.property⟩
  left_inv u := Subtype.ext (ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val)
  right_inv u := Subtype.ext (ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val)
  map_add' u v := Subtype.ext ((ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)).map_add u.val v.val)
  map_smul' z u := Subtype.ext (ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_smul (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) z u.val)

theorem conjugatePeriodKernel_finrank : Module.finrank ℂ (conjugatePeriodKernel A) =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
  let e : (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker ≃ₗ[ℝ] conjugatePeriodKernel A :=
    { (periodKernelConjugation A).toEquiv with
      map_add' := (periodKernelConjugation A).map_add
      map_smul' := by
        intro r u
        apply Subtype.ext
        change ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (r • u.val) =
          r • ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val
        have hl := congrArg (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
          (IsScalarTower.algebraMap_smul ℂ r u.val)
        have hc := ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_smul (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (r : ℂ) u.val
        have hs : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
        have hr := congrArg (fun z : ℂ => z • ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val) hs
        exact hl.symm.trans (hc.trans (hr.trans
          (IsScalarTower.algebraMap_smul ℂ r (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u.val)))) }
  have hleft := Module.finrank_mul_finrank ℝ ℂ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker
  have hright := Module.finrank_mul_finrank ℝ ℂ (conjugatePeriodKernel A)
  have heq := e.finrank_eq
  rw [Complex.finrank_real_complex, Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_ker_finrank] at hleft
  rw [Complex.finrank_real_complex] at hright
  omega

theorem nativePeriodKernels_disjoint : Disjoint (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker (conjugatePeriodKernel A) := by
  apply Submodule.disjoint_def.mpr
  intro u hu hc
  exact complexPeriodProjection_conjugate_joint_zero A u hu hc

theorem nativePeriodKernels_complementary : IsCompl (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker (conjugatePeriodKernel A) := by
  refine ⟨nativePeriodKernels_disjoint A, ?_⟩
  apply codisjoint_iff.mpr
  apply Submodule.eq_top_of_finrank_eq
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker (conjugatePeriodKernel A)
  have hbot : (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker ⊓ conjugatePeriodKernel A = ⊥ :=
    (nativePeriodKernels_disjoint A).eq_bot
  have hall : Module.finrank ℂ (ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) =
      2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
    rw [Module.finrank_eq_card_basis (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodBasis A), Fintype.card_fin]
  rw [hbot, finrank_bot, add_zero, Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_ker_finrank, conjugatePeriodKernel_finrank] at hd
  exact hd.trans (by omega)

def nativePeriodHodgeStructure : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) where
  holomorphic := (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker
  antiholomorphic := conjugatePeriodKernel A
  complementary := nativePeriodKernels_complementary A
  conjugate_mem u := by
    change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) u)) = 0 ↔ Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u = 0
    rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods
