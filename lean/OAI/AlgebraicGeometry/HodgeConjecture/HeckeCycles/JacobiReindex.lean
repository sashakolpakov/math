import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Jacobi Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.JacobiReindex.CM

noncomputable section

/-! The actual Jacobi substitution and quadratic correction are invariant
under a simultaneous relabeling of the symplectic matrix and period. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J) (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks J ℝ) (h : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ)
  (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) (W : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
  (hM : (Matrix.fromBlocks g.A g.B g.C g.D).submatrix (e.sumCongr e) (e.sumCongr e) =
    Matrix.fromBlocks h.A h.B h.C h.D)
  (hZ : Z.matrix.submatrix e e = W.matrix)

include hM in
theorem lower_left : g.complexify.C.submatrix e e = h.complexify.C := by
  ext i j
  exact congrArg (algebraMap ℝ ℂ) (congrFun (congrFun hM (.inr i)) (.inl j))

include hM in
theorem lower_right : g.complexify.D.submatrix e e = h.complexify.D := by
  ext i j
  exact congrArg (algebraMap ℝ ℂ) (congrFun (congrFun hM (.inr i)) (.inr j))

include hM hZ in
theorem denominator : (g.complexify.denominator Z.matrix).submatrix e e = h.complexify.denominator W.matrix := by
  change (g.complexify.C * Z.matrix + g.complexify.D).submatrix e e = _
  simp only [Matrix.submatrix_add, Pi.add_apply]
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,
    lower_left e g h hM, lower_right e g h hM, hZ]
  rfl

include hM hZ in
theorem inverse_denominator : ((g.complexify.denominator Z.matrix)⁻¹).submatrix e e =
    (h.complexify.denominator W.matrix)⁻¹ := by
  rw [← Matrix.inv_submatrix_equiv, CM.denominator e g h Z W hM hZ]

include hM hZ in
theorem jacobi (ξ : J → ℂ) : (g.jacobiChange Z ξ) ∘ e = h.jacobiChange W (ξ ∘ e) := by
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply]
  have hv := Matrix.submatrix_mulVec_equiv ((g.complexify.denominator Z.matrix)⁻¹).transpose
    (ξ ∘ e) e e
  simp only [Function.comp_def, Equiv.apply_symm_apply] at hv
  have hm : (((g.complexify.denominator Z.matrix)⁻¹).transpose).submatrix e e =
      ((h.complexify.denominator W.matrix)⁻¹).transpose :=
    congrArg Matrix.transpose (inverse_denominator e g h Z W hM hZ)
  rw [hm] at hv
  exact hv.symm

include hM hZ in
theorem correction (ξ η : J → ℂ) :
    g.thetaCorrectionForm Z ξ η = h.thetaCorrectionForm W (ξ ∘ e) (η ∘ e) := by
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply]
  apply congrArg (fun c : ℂ => (Real.pi : ℂ) * Complex.I * c)
  have hm : ((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C).submatrix e e =
      (h.complexify.denominator W.matrix)⁻¹ * h.complexify.C := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      inverse_denominator e g h Z W hM hZ, lower_left e g h hM]
  have hv := Matrix.submatrix_mulVec_equiv
    ((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) (η ∘ e) e e
  simp only [Function.comp_def, Equiv.apply_symm_apply] at hv
  rw [hm] at hv
  exact ((e.sum_comp (fun j => ξ j *
    (((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) *ᵥ η) j)).symm).trans
      (congrArg (fun v : I → ℂ => (ξ ∘ e) ⬝ᵥ v) hv.symm)

include hM hZ in
theorem quadratic (ξ : J → ℂ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor g Z ξ = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor h W (ξ ∘ e) :=
  congrArg Complex.exp (correction e g h Z W hM hZ ξ ξ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.JacobiReindex.CM
