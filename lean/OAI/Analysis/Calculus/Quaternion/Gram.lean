import OAI.Analysis.Calculus.Quaternion.Holomorphic

namespace OAI.Analysis.Calculus.Quaternion

noncomputable section
open scoped Matrix

theorem quaternionGram_quadratic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι Q) (x : ι → Q) :
    (star x ⬝ᵥ ((Jᴴ * J) *ᵥ x)).re = ∑ i, Quaternion.normSq ((J *ᵥ x) i) := by
  classical
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  change (∑ i, star ((J *ᵥ x) i) * (J *ᵥ x) i).re = _
  simp only [Quaternion.star_mul_self]
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem quaternionGram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι Q) (x : ι → Q) : 0 ≤ (star x ⬝ᵥ ((Jᴴ * J) *ᵥ x)).re := by
  rw [quaternionGram_quadratic]
  exact Finset.sum_nonneg (fun _ _ => Quaternion.normSq_nonneg)

theorem quaternionGram_kernel {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι Q) (x : ι → Q) : (Jᴴ * J) *ᵥ x = 0 ↔ J *ᵥ x = 0 := by
  constructor
  · intro h
    have he := quaternionGram_quadratic J x
    rw [h] at he
    simp only [dotProduct_zero, Quaternion.re_zero] at he
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      (Quaternion.normSq_nonneg : 0 ≤ Quaternion.normSq ((J *ᵥ x) i)))).mp he.symm
    funext i
    exact Quaternion.normSq_eq_zero.mp (hz i (Finset.mem_univ i))
  · intro h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem quaternionGram_pos {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι Q) (x : ι → Q) (hx : J *ᵥ x ≠ 0) :
    0 < (star x ⬝ᵥ ((Jᴴ * J) *ᵥ x)).re := by
  rw [quaternionGram_quadratic]
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => Quaternion.normSq_nonneg))
  intro hz
  apply hx
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    (Quaternion.normSq_nonneg : 0 ≤ Quaternion.normSq ((J *ᵥ x) i)))).mp hz.symm
  funext i
  exact Quaternion.normSq_eq_zero.mp (hi i (Finset.mem_univ i))

end
end OAI.Analysis.Calculus.Quaternion
