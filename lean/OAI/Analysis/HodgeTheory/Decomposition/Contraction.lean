import OAI.Analysis.HodgeTheory.Decomposition.CovectorPair
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Contraction -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Contraction.Constructions

noncomputable section

/-! A fixed-coordinate expression for the intrinsic covector metric. It uses
the inverse Gram matrix, avoiding any need to differentiate a chosen orthonormal basis. -/

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
theorem real_dual_frame_coordinates (b : Module.Basis ι ℝ E) (w : ι → E)
    (hw : ∀ i j, inner ℝ (w i) (b j) = if i = j then 1 else 0) (x : E) (i : ι) :
    inner ℝ (w i) x = b.repr x i := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [inner_sum, inner_smul_right, hw]
  simp

omit [FiniteDimensional ℝ E] in
theorem covector_dual_frame_expansion (b : Module.Basis ι ℝ E) (w : ι → E)
    (hw : ∀ i j, inner ℝ (w i) (b j) = if i = j then 1 else 0)
    (f : E →ₗ[ℝ] ℂ) (x : E) :
    f x = ∑ i, (inner ℝ (w i) x : ℂ) * f (b i) := by
  simp_rw [real_dual_frame_coordinates b w hw]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, Complex.real_smul]

/-- Contraction against a real metric-dual frame computes the intrinsic Hermitian pairing. -/
theorem covectorInner_dual_frame (b : Module.Basis ι ℝ E) (w : ι → E)
    (hw : ∀ i j, inner ℝ (w i) (b j) = if i = j then 1 else 0)
    (f g : E →ₗ[ℝ] ℂ) :
    CovectorPair.Constructions.covectorInner f g =
      ∑ j, ∑ k, star (f (b k)) * (inner ℝ (w k) (w j) : ℂ) * g (b j) := by
  let c := stdOrthonormalBasis ℝ E
  have hsum (j k : ι) :
      ∑ l, (inner ℝ (w k) (c l) : ℂ) * (inner ℝ (w j) (c l) : ℂ) =
        (inner ℝ (w k) (w j) : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) (c.sum_inner_mul_inner (w k) (w j))
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, real_inner_comm (c _) (w j)] using h
  change (∑ l, star (f (c l)) * g (c l)) = _
  conv_lhs =>
    enter [2, l]
    rw [covector_dual_frame_expansion b w hw f (c l), covector_dual_frame_expansion b w hw g (c l)]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hsum j k, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

def inverseGramFrame (b : Module.Basis ι ℝ E) (i : ι) : E :=
  ∑ j, (Matrix.gram ℝ b)⁻¹ i j • b j

omit [FiniteDimensional ℝ E] in
theorem inverseGramFrame_dual (b : Module.Basis ι ℝ E) (i j : ι) :
    inner ℝ (inverseGramFrame b i) (b j) = if i = j then 1 else 0 := by
  have hdet : IsUnit (Matrix.gram ℝ b).det :=
    isUnit_iff_ne_zero.mpr ((Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')
  have h := congrArg (fun A : Matrix ι ι ℝ => A i j) (Matrix.nonsing_inv_mul (Matrix.gram ℝ b) hdet)
  simpa only [inverseGramFrame, sum_inner, inner_smul_left, RCLike.conj_to_real,
    Matrix.mul_apply, Matrix.gram_apply, Matrix.one_apply] using h

omit [FiniteDimensional ℝ E] in
theorem inverseGramFrame_inner (b : Module.Basis ι ℝ E) (i j : ι) :
    inner ℝ (inverseGramFrame b i) (inverseGramFrame b j) = (Matrix.gram ℝ b)⁻¹ j i := by
  conv_lhs => rhs; rw [inverseGramFrame]
  simp only [inner_sum, inner_smul_right, inverseGramFrame_dual]
  simp

/-- The coordinate formula uses the genuine inverse metric on the covector indices. -/
theorem covectorInner_inverse_gram (b : Module.Basis ι ℝ E) (f g : E →ₗ[ℝ] ℂ) :
    CovectorPair.Constructions.covectorInner f g =
      ∑ j, ∑ k, star (f (b k)) * ((Matrix.gram ℝ b)⁻¹ j k : ℂ) * g (b j) := by
  rw [covectorInner_dual_frame b (inverseGramFrame b) (inverseGramFrame_dual b)]
  simp only [inverseGramFrame_inner]

end

end OAI.Analysis.HodgeTheory.Decomposition.Contraction.Constructions
