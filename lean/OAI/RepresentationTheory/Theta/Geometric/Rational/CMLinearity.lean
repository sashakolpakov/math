import Mathlib.NumberTheory.NumberField.Basic

/-! # CM Linearity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity

noncomputable section

/-! A rational linear map commuting with the integral CM action is
linear over the entire field, by the actual integral number-field basis. -/

variable {E V W : Type*} [Field E] [NumberField E]
    [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]
    [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

theorem rationalMap_integral_scalar_extension (f : V →ₗ[ℚ] W)
    (hf : ∀ (a : NumberField.RingOfIntegers E) (v : V), f ((a : E) • v) = (a : E) • f v)
    (a : E) (v : V) : f (a • v) = a • f v := by
  let l : E →ₗ[ℚ] W := f.comp ((LinearMap.toSpanSingleton E V v).restrictScalars ℚ)
  let r : E →ₗ[ℚ] W := (LinearMap.toSpanSingleton E W (f v)).restrictScalars ℚ
  have he : l = r := by
    apply (NumberField.integralBasis E).ext
    intro i
    change f (NumberField.integralBasis E i • v) = NumberField.integralBasis E i • f v
    rw [NumberField.integralBasis_apply]
    exact hf (NumberField.RingOfIntegers.basis E i) v
  exact LinearMap.congr_fun he a

def rationalMapToCMLinear (f : V →ₗ[ℚ] W)
    (hf : ∀ (a : NumberField.RingOfIntegers E) (v : V), f ((a : E) • v) = (a : E) • f v) : V →ₗ[E] W where
  toFun := f
  map_add' := f.map_add
  map_smul' := rationalMap_integral_scalar_extension f hf

end

end OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity
