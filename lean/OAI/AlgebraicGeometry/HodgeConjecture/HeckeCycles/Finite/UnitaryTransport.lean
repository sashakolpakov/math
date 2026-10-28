import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeVolumes

/-! # Unitary Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryTransport.CM

noncomputable section

/-! Normalize pullback along an actual continuous linear change of
finite adelic coordinates to a unitary automorphism of the test space. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

variable {I : Type*} [Fintype I]

def factor (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : NNReal :=
  Measure.addHaarScalarFactor ((Constructed.FiniteMeasure.CM.measure I).map e) (Constructed.FiniteMeasure.CM.measure I)

theorem factor_pos (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : 0 < factor e :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem integral_change (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    (∫ x, f (e x) ∂(Constructed.FiniteMeasure.CM.measure I)) = (factor e : ℂ) * ∫ x, f x ∂(Constructed.FiniteMeasure.CM.measure I) := by
  have he := e.toHomeomorph.isClosedEmbedding.integral_map (μ := Constructed.FiniteMeasure.CM.measure I) f
  change (∫ x, f x ∂((Constructed.FiniteMeasure.CM.measure I).map e)) = ∫ x, f (e x) ∂(Constructed.FiniteMeasure.CM.measure I) at he
  rw [← he]
  rw [Measure.isAddLeftInvariant_eq_smul ((Constructed.FiniteMeasure.CM.measure I).map e) (Constructed.FiniteMeasure.CM.measure I),
    integral_smul_nnreal_measure]
  rfl

def scalar (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℝ := (Real.sqrt (factor e : ℝ))⁻¹

theorem scalar_ne_zero (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : scalar e ≠ 0 := by
  apply inv_ne_zero
  exact (Real.sqrt_pos.mpr (by exact_mod_cast factor_pos e)).ne'

theorem scalar_sq (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : scalar e ^ 2 * (factor e : ℝ) = 1 := by
  have hc : (factor e : ℝ) ≠ 0 := by exact_mod_cast (factor_pos e).ne'
  have hs : (Real.sqrt (factor e : ℝ)) ^ 2 = (factor e : ℝ) := Real.sq_sqrt (factor e).property
  unfold scalar
  rw [inv_pow, hs, inv_mul_cancel₀ hc]

def pullback (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  ⟨f.val ∘ e, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
    ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp f.property).1.comp_continuous e.continuous,
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).comp_homeomorph e.toHomeomorph⟩⟩

def pullbackEquiv (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I where
  toFun := pullback e
  invFun := pullback e.symm
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (e (e.symm x)) = f.val x
    rw [e.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (e.symm (e x)) = f.val x
    rw [e.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def transport (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  (pullbackEquiv e).trans
    (LinearEquiv.smulOfNeZero ℂ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (scalar e : ℂ)
      (Complex.ofReal_ne_zero.mpr (scalar_ne_zero e)))

theorem transport_apply (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (transport e f).val x = (scalar e : ℂ) * f.val (e x) := rfl

theorem unitary (e : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.integralPairing (transport e f) (transport e h) = FiniteOscillator.CM.integralPairing f h := by
  have ha : (scalar e : ℂ) * star (scalar e : ℂ) * (factor e : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_ofReal, ← pow_two]
    exact_mod_cast scalar_sq e
  change (∫ x, (transport e f).val x * star ((transport e h).val x) ∂(Constructed.FiniteMeasure.CM.measure I)) = _
  simp_rw [transport_apply, star_mul]
  calc
    _ = ((scalar e : ℂ) * star (scalar e : ℂ)) *
        ∫ x, f.val (e x) * star (h.val (e x)) ∂(Constructed.FiniteMeasure.CM.measure I) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [integral_change e (fun x => f.val x * star (h.val x)), ← mul_assoc, ha, one_mul]
      rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryTransport.CM
