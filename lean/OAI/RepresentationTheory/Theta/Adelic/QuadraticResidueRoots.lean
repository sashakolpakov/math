import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase

/-! # Quadratic Residue Roots -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticResidueRoots

noncomputable section

/-! Root homomorphisms and a norm criterion over an arbitrary residue
field. No characteristic-zero assumption is used. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction

variable {k : Type*} [Field k] {d : k} (r : k) (hr : r ^ 2 = d)

def rootHom : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d →+* k where
  toFun z := z.re + r * z.im
  map_zero' := by simp
  map_one' := by simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, mul_zero, add_zero]
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero]
    linear_combination -(z.im * w.im) * hr

theorem rootHom_norm (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    rootHom r hr z * rootHom (-r) (by simpa using hr) z = QuadraticAlgebra.norm z := by
  change (z.re + r * z.im) * (z.re + (-r) * z.im) =
    z.re * z.re + 0 * z.re * z.im - d * z.im * z.im
  linear_combination -(z.im ^ 2) * hr

theorem rootHom_isUnit (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)
    (hp : rootHom r hr z ≠ 0) (hm : rootHom (-r) (by simpa using hr) z ≠ 0) : IsUnit z := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  apply isUnit_iff_ne_zero.mpr
  rw [← rootHom_norm r hr]
  exact mul_ne_zero hp hm

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticResidueRoots
