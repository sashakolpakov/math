import Mathlib

/-! # Matrix Calculus -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM

noncomputable section

/-! Holomorphic dependence of the actual finite period matrices, in the
elementwise matrix topology used by the theta constructions. -/

open scoped Classical _root_.Matrix.Norms.Elementwise

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [Fintype ι] [DecidableEq ι] {s : Set V}

theorem matrix_determinant_holomorphic (M : V → Matrix ι ι ℂ)
    (hM : DifferentiableOn ℂ M s) : DifferentiableOn ℂ (fun z => (M z).det) s := by
  simp only [Matrix.det_apply']
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.mul (differentiableOn_const _)
  have hp (t : Finset ι) : DifferentiableOn ℂ (fun z => ∏ i ∈ t, M z (σ i) i) s := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiableOn_const (1 : ℂ))
    | @insert a t hat ih =>
      simp only [Finset.prod_insert hat]
      exact ((differentiable_apply a).comp_differentiableOn
        ((differentiable_apply (σ a)).comp_differentiableOn hM)).mul ih
  exact hp Finset.univ

theorem matrix_inverse_holomorphic (M : V → Matrix ι ι ℂ)
    (hM : DifferentiableOn ℂ M s) (hdet : ∀ z ∈ s, (M z).det ≠ 0) :
    DifferentiableOn ℂ (fun z => (M z)⁻¹) s := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply DifferentiableOn.mul
  · exact (matrix_determinant_holomorphic M hM).inv hdet
  · apply matrix_determinant_holomorphic
    apply differentiableOn_pi.mpr
    intro k
    apply differentiableOn_pi.mpr
    intro l
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableOn_const _
    · fun_prop

omit [DecidableEq ι] in
theorem matrix_product_holomorphic (M N : V → Matrix ι ι ℂ)
    (hM : DifferentiableOn ℂ M s) (hN : DifferentiableOn ℂ N s) :
    DifferentiableOn ℂ (fun z => M z * N z) s := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  fun_prop

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM
