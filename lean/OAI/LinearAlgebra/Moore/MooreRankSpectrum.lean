import OAI.LinearAlgebra.Moore.MooreRankProduct

noncomputable section
open scoped Matrix ComplexOrder
namespace OAI.LinearAlgebra.Moore

theorem eigenvalues_le_of_scalar_sub_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {M : ℝ}
    (hupper : (M • (1 : Matrix ι ι ℂ) - A).PosSemidef) (i : ι) :
    hA.eigenvalues i ≤ M := by
  let v : ι → ℂ := ⇑(hA.eigenvectorBasis i)
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    change star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
    simp [hA.eigenvectorBasis.orthonormal.1 i]
  have he : (star v ⬝ᵥ (A *ᵥ v)).re = hA.eigenvalues i :=
    (hA.eigenvalues_eq i).symm
  have hh := hupper.re_dotProduct_nonneg v
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, hv] at hh
  rw [← he]
  simpa using hh

theorem det_add_scalar_eq_prod_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (a : ℝ) :
    (A + a • (1 : Matrix ι ι ℂ)).det.re = ∏ i, (hA.eigenvalues i + a) := by
  let U := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hd : A = (U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ) := by
    exact hA.spectral_theorem
  have he : A + a • (1 : Matrix ι ι ℂ) =
      (U : Matrix ι ι ℂ) * (D + a • 1) * star (U : Matrix ι ι ℂ) := by
    rw [Matrix.mul_add, Matrix.add_mul, ← hd]
    simp []
  have hdiag : D + a • (1 : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => ((hA.eigenvalues i + a : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  rw [he, Matrix.det_mul, Matrix.det_mul]
  have hu : (U : Matrix ι ι ℂ).det * (star (U : Matrix ι ι ℂ)).det = 1 := by
    rw [← Matrix.det_mul]
    simp
  rw [mul_assoc, mul_comm (D + a • (1 : Matrix ι ι ℂ)).det, ← mul_assoc, hu,
    one_mul, hdiag, Matrix.det_diagonal, ← Complex.ofReal_prod]
  rfl

theorem complex_det_add_scalar_le_of_rank
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) {M a : ℝ} {r : ℕ}
    (hupper : (M • (1 : Matrix ι ι ℂ) - A).PosSemidef)
    (hr : A.rank ≤ r) (hrN : r ≤ Fintype.card ι) (hM : 0 ≤ M) (ha : 0 ≤ a) :
    (A + a • (1 : Matrix ι ι ℂ)).det.re ≤
      (M + a) ^ r * a ^ (Fintype.card ι - r) := by
  rw [det_add_scalar_eq_prod_eigenvalues hA.isHermitian]
  apply product_shift_le_of_support _ (hA.eigenvalues_nonneg) hM
    (eigenvalues_le_of_scalar_sub_posSemidef hA.isHermitian hupper) ha
    _ hrN
  simpa only [← hA.isHermitian.rank_eq_card_non_zero_eigs] using hr

end OAI.LinearAlgebra.Moore
