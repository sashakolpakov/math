import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFrameFamilies

/-! # Period Matrix Families -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodMatrixFamilies.Multiplicity

noncomputable section

/-! Holomorphic matrix operations used to turn actual positive frames
into a period family. Invertibility is required only on the chart domain. -/

open scoped Classical _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart} {A B : Geometry.ComplexBall.PrescribedSignsB.BallChart → Matrix ι ι ℂ}

theorem matrix_family_det_differentiable (hA : DifferentiableOn ℂ A O) :
    DifferentiableOn ℂ (fun z => (A z).det) O := by
  have hentry (i j : ι) : DifferentiableOn ℂ (fun z => A z i j) O :=
    differentiableOn_pi.mp (differentiableOn_pi.mp hA i) j
  simp only [Matrix.det_apply']
  have ht (σ : Equiv.Perm ι) : DifferentiableOn ℂ
      (fun z => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i) O := by
    have hp (t : Finset ι) : DifferentiableOn ℂ (fun z => ∏ i ∈ t, A z (σ i) i) O := by
      induction t using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (differentiableOn_const (1 : ℂ) (s := O))
      | @insert i t hi ih =>
          simp only [Finset.prod_insert hi]
          exact (hentry (σ i) i).mul ih
    exact (differentiableOn_const _ : DifferentiableOn ℂ
      (fun _ : Geometry.ComplexBall.PrescribedSignsB.BallChart => ((Equiv.Perm.sign σ : ℤ) : ℂ)) O).mul
      (hp Finset.univ)
  have he : (fun z : Geometry.ComplexBall.PrescribedSignsB.BallChart => ∑ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i) =
      ∑ σ : Equiv.Perm ι, (fun z : Geometry.ComplexBall.PrescribedSignsB.BallChart => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i) := by
    funext z
    rw [Finset.sum_apply]
  rw [he]
  exact DifferentiableOn.sum (u := Finset.univ) (fun σ _ => ht σ)

theorem matrix_family_adjugate_differentiable (hA : DifferentiableOn ℂ A O) :
    DifferentiableOn ℂ (fun z => (A z).adjugate) O := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply matrix_family_det_differentiable
  apply differentiableOn_pi.mpr
  intro k
  apply differentiableOn_pi.mpr
  intro l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact differentiableOn_pi.mp (differentiableOn_pi.mp hA k) l

theorem matrix_family_inverse_differentiable (hA : DifferentiableOn ℂ A O)
    (hdet : ∀ z ∈ O, (A z).det ≠ 0) : DifferentiableOn ℂ (fun z => (A z)⁻¹) O := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  exact ((matrix_family_det_differentiable hA).inv hdet).mul
    (differentiableOn_pi.mp (differentiableOn_pi.mp (matrix_family_adjugate_differentiable hA) i) j)

omit [DecidableEq ι] in
theorem matrix_family_mul_differentiable (hA : DifferentiableOn ℂ A O)
    (hB : DifferentiableOn ℂ B O) : DifferentiableOn ℂ (fun z => A z * B z) O := by
  have ha (i j : ι) : DifferentiableOn ℂ (fun z => A z i j) O :=
    differentiableOn_pi.mp (differentiableOn_pi.mp hA i) j
  have hb (i j : ι) : DifferentiableOn ℂ (fun z => B z i j) O :=
    differentiableOn_pi.mp (differentiableOn_pi.mp hB i) j
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  fun_prop

theorem frame_graph_differentiable (hA : DifferentiableOn ℂ A O)
    (hB : DifferentiableOn ℂ B O) (hdet : ∀ z ∈ O, (B z).det ≠ 0) :
    DifferentiableOn ℂ (fun z => A z * (B z)⁻¹) O :=
  matrix_family_mul_differentiable hA (matrix_family_inverse_differentiable hB hdet)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodMatrixFamilies.Multiplicity
