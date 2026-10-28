import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Even Characteristic Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EvenCharacteristicEvaluation

noncomputable section

/-! In even rank, the characteristic polynomial at -c is the determinant
of c+F. This is the exact sign normalization for geometric plus-shifts. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem eval_neg (F : Module.End K V) (c : K) (h : Even (Module.finrank K V)) :
    F.charpoly.eval (-c) = (algebraMap K (Module.End K V) c + F).det := by
  rw [LinearMap.eval_charpoly, map_neg, sub_eq_add_neg, ← neg_add]
  have he : -(algebraMap K (Module.End K V) c + F) =
      (-1 : K) • (algebraMap K (Module.End K V) c + F) := by simp [add_comm]
  rw [he, LinearMap.det_smul, h.neg_one_pow, one_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EvenCharacteristicEvaluation
