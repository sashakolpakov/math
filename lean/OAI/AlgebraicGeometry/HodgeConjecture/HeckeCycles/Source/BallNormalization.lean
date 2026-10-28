import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.RepresentationTheory.Theta.Adelic.BallNatural

/-! # Ball Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallNormalization.CM

noncomputable section

/-! The original weighted ball is explicitly identified with the unit
ball used by AdelicTheta, through its actual negative Hermitian coefficient. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (B : GeometricSource.CM.BallDatum E)

def radius : ℝ := Real.sqrt (-(B.b : ℂ).re)

theorem radius_pos : 0 < radius E B := Real.sqrt_pos.mpr (neg_pos.mpr B.negative)

theorem radius_ne_zero : radius E B ≠ 0 := ne_of_gt (radius_pos E B)

theorem radius_square : radius E B ^ 2 = -(B.b : ℂ).re :=
  Real.sq_sqrt (le_of_lt (neg_pos.mpr B.negative))

def normalize (z : GeometricSource.CM.BallChart) : GeometricSource.CM.BallChart := fun i => z i / (radius E B : ℂ)

def denormalize (z : GeometricSource.CM.BallChart) : GeometricSource.CM.BallChart := fun i => (radius E B : ℂ) * z i

theorem normalize_norm (z : GeometricSource.CM.BallChart) :
    Complex.normSq (normalize E B z 0) + Complex.normSq (normalize E B z 1) =
      (Complex.normSq (z 0) + Complex.normSq (z 1)) / (radius E B ^ 2) := by
  simp only [normalize, Complex.normSq_div, Complex.normSq_ofReal, ← add_div, pow_two]

theorem normalize_mem (z : GeometricSource.CM.BallChart) :
    Complex.normSq (normalize E B z 0) + Complex.normSq (normalize E B z 1) < 1 ↔ z ∈ B.domain := by
  rw [normalize_norm, div_lt_one (sq_pos_of_ne_zero (radius_ne_zero E B)), radius_square]
  rfl

theorem normalize_denormalize (z : GeometricSource.CM.BallChart) : normalize E B (denormalize E B z) = z := by
  funext i
  exact mul_div_cancel_left₀ (z i) (Complex.ofReal_ne_zero.mpr (radius_ne_zero E B))

theorem denormalize_normalize (z : GeometricSource.CM.BallChart) : denormalize E B (normalize E B z) = z := by
  funext i
  exact mul_div_cancel₀ (z i) (Complex.ofReal_ne_zero.mpr (radius_ne_zero E B))

def equiv : B.Domain ≃ RepresentationTheory.Theta.Adelic.BallNatural.Ball where
  toFun z := ⟨normalize E B z.val, (normalize_mem E B z.val).mpr z.property⟩
  invFun z := ⟨denormalize E B z.val, (normalize_mem E B _).mp (by
    rw [normalize_denormalize]
    exact z.property)⟩
  left_inv z := Subtype.ext (denormalize_normalize E B z.val)
  right_inv z := Subtype.ext (normalize_denormalize E B z.val)

theorem normalize_continuous : Continuous (normalize E B) := by
  unfold normalize
  fun_prop

theorem denormalize_continuous : Continuous (denormalize E B) := by
  unfold denormalize
  fun_prop

def homeomorph : B.Domain ≃ₜ RepresentationTheory.Theta.Adelic.BallNatural.Ball where
  toEquiv := equiv E B
  continuous_toFun := ((normalize_continuous E B).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((denormalize_continuous E B).comp continuous_subtype_val).subtype_mk _

theorem normalize_holomorphic : Differentiable ℂ (normalize E B) := by
  unfold normalize
  fun_prop

theorem denormalize_holomorphic : Differentiable ℂ (denormalize E B) := by
  unfold denormalize
  fun_prop

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallNormalization.CM
