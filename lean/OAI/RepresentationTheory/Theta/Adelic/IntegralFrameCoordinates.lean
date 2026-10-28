import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace
import OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

/-! # Integral Frame Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralFrameCoordinates

noncomputable section

/-! Finite coordinate criteria for a frame and its inverse to preserve
the integral tensor and phase lattices. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction

variable {k I J : Type*} [Field k] [Fintype I] [DecidableEq I]
variable [Fintype J] [DecidableEq J] (d : k)

omit [Fintype J] [DecidableEq J] in
theorem quadratic_vector_expansion (x : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    x = (∑ i, (x i).re • Pi.single i (1 : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) +
      ∑ i, (x i).im • Pi.single i (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d) := by
  funext j
  apply QuadraticAlgebra.ext <;>
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, Weil.AdelicSplitting.Integral.Construction.quadraticGenerator,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

omit [Fintype J] [DecidableEq J] in
theorem linear_coordinates_integral (S : Subring k)
    (L : (I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) →ₗ[k] (J → k))
    (hr : ∀ i j, L (Pi.single i 1) j ∈ S)
    (hi : ∀ i j, L (Pi.single i (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d)) j ∈ S)
    (x : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (hx : ∀ i, (x i).re ∈ S ∧ (x i).im ∈ S) :
    ∀ j, L x j ∈ S := by
  have he := congrArg L (quadratic_vector_expansion d x)
  simp only [map_add, map_sum, map_smul] at he
  intro j
  rw [he]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact S.add_mem (S.sum_mem fun i _ => S.mul_mem (hx i).1 (hr i j))
    (S.sum_mem fun i _ => S.mul_mem (hx i).2 (hi i j))

omit [Fintype I] [DecidableEq I] in
theorem inverse_coordinates_integral (S : Subring k) (T : Subring (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (hscalar : ∀ a ∈ S, algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) a ∈ T)
    (L : (J → k) →ₗ[k] (I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (hL : ∀ j i, L (Pi.single j 1) i ∈ T)
    (x : J → k) (hx : ∀ j, x j ∈ S) : ∀ i, L x i ∈ T := by
  have he : x = ∑ j, x j • Pi.single j (1 : k) := by
    ext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have hmap := congrArg L he
  simp only [map_sum, map_smul] at hmap
  intro i
  rw [hmap]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply T.sum_mem
  intro j _
  rw [Algebra.smul_def]
  exact T.mul_mem (hscalar (x j) (hx j)) (hL j i)

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralFrameCoordinates
