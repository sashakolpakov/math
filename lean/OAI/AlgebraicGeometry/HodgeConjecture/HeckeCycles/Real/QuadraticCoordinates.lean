import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology
import Mathlib.Analysis.Complex.Basic

/-! # Quadratic Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.QuadraticCoordinates.CM

noncomputable section

/-! Explicit coordinates on a quadratic algebra over a real completion,
with the sign of its imaginary generator retained. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction

variable {k : Type*} [Field k] (e : k ≃+* ℝ) (d : k) (t : ℝ)
  (hd : e d = -(t ^ 2)) (ht : t ≠ 0)

def equivalence : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃+* ℂ where
  toFun z := (e z.re : ℂ) + (e z.im : ℂ) * (t : ℂ) * Complex.I
  invFun z := ⟨e.symm z.re, e.symm (z.im / t)⟩
  left_inv z := by
    apply QuadraticAlgebra.ext
    · simp
    · simp [ht]
  right_inv z := by
    apply Complex.ext
    · simp
    · simp [ht]
  map_mul' z w := by
    apply Complex.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hd, pow_two] <;> ring
  map_add' z w := by
    apply Complex.ext <;> simp
    ring

theorem apply (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) : equivalence e d t hd ht z =
    (e z.re : ℂ) + (e z.im : ℂ) * (t : ℂ) * Complex.I := rfl

theorem scalar (x : k) :
    equivalence e d t hd ht (algebraMap k (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) x) = (e x : ℂ) := by
  simp [CM.apply]

theorem star (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    equivalence e d t hd ht (star z) = star (equivalence e d t hd ht z) := by
  apply Complex.ext <;> simp [CM.apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

variable [TopologicalSpace k]

theorem continuous (he : Continuous e) : Continuous (equivalence e d t hd ht) :=
  (Complex.continuous_ofReal.comp (he.comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d))).add
    (((Complex.continuous_ofReal.comp (he.comp (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d))).mul
      continuous_const).mul continuous_const)

theorem inverse_continuous (he : Continuous e.symm) : Continuous (equivalence e d t hd ht).symm := by
  rw [RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  exact ⟨he.comp Complex.continuous_re, he.comp (Complex.continuous_im.div_const t)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.QuadraticCoordinates.CM
