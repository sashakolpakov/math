import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ScaleMeasure
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator

/-! # Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Dilation.CM

noncomputable section

/-! Rational dilation as an actual unitary automorphism of the finite
Schwartz space, normalized using the constructed finite Haar measure. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ScaleMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

variable {I : Type*} [Fintype I]

def pullback (q : ℚ) (hq : q ≠ 0) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  ⟨f.val ∘ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
    ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp f.property).1.comp_continuous (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q),
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).comp_homeomorph (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScaleHomeomorph q hq)⟩⟩

def pullbackEquiv (q : ℚ) (hq : q ≠ 0) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I where
  toFun := pullback q hq
  invFun := pullback q⁻¹ (inv_ne_zero hq)
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q⁻¹ x)) = f.val x
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_mul, mul_inv_cancel₀ hq, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_one]
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q⁻¹ (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x)) = f.val x
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_mul, inv_mul_cancel₀ hq, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dilation (q : ℚ) (hq : q ≠ 0) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  (pullbackEquiv q hq).trans
    (LinearEquiv.smulOfNeZero ℂ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
      (ScaleMeasure.CM.normalizingScalar (I := I) q hq : ℂ)
      (Complex.ofReal_ne_zero.mpr (ScaleMeasure.CM.normalizingScalar_ne_zero q hq)))

theorem dilation_apply (q : ℚ) (hq : q ≠ 0) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (dilation q hq f).val x =
      (ScaleMeasure.CM.normalizingScalar (I := I) q hq : ℂ) * f.val (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x) := rfl

theorem unitary (q : ℚ) (hq : q ≠ 0) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.integralPairing (dilation q hq f) (dilation q hq h) = FiniteOscillator.CM.integralPairing f h := by
  let a := ScaleMeasure.CM.normalizingScalar (I := I) q hq
  have ha : (a : ℂ) * star (a : ℂ) * (ScaleMeasure.CM.factor (I := I) q hq : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_ofReal, ← pow_two]
    exact_mod_cast ScaleMeasure.CM.normalizingScalar_sq (I := I) q hq
  change (∫ x, (dilation q hq f).val x * star ((dilation q hq h).val x) ∂(Constructed.FiniteMeasure.CM.measure I)) = _
  simp_rw [dilation_apply, star_mul]
  calc
    _ = ((a : ℂ) * star (a : ℂ)) *
        ∫ x, f.val (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x) * star (h.val (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x)) ∂(Constructed.FiniteMeasure.CM.measure I) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp only [a]; ring
    _ = _ := by
      rw [ScaleMeasure.CM.integral_scale q hq (fun x => f.val x * star (h.val x)), ← mul_assoc, ha, one_mul]
      rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Dilation.CM
