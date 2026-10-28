import OAI.Analysis.PDE.Elliptic.HessianTrace

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform ellipticity tested on vectors controls the trace pairing with
every positive semidefinite Hessian. No regularity of the coefficients is
required for this algebraic step. -/
theorem trace_comp_lower_of_positive (A H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsPositive) {lam : ℝ}
    (hA : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A v)) :
    lam * LinearMap.trace ℝ E H.toLinearMap ≤
      LinearMap.trace ℝ E (A.comp H).toLinearMap := by
  let b := hH.isSymmetric.eigenvectorBasis rfl
  let e := hH.isSymmetric.eigenvalues rfl
  have he (i : Fin (Module.finrank ℝ E)) : 0 ≤ e i := by
    exact eigenvalue_nonneg_of_nonneg (hH.isSymmetric.hasEigenvalue_eigenvalues rfl i)
      hH.re_inner_nonneg_right
  have hHb (i : Fin (Module.finrank ℝ E)) : H (b i) = e i • b i :=
    hH.isSymmetric.apply_eigenvectorBasis rfl i
  rw [hH.isSymmetric.trace_eq_sum_eigenvalues rfl, LinearMap.trace_eq_sum_inner _ b]
  change lam * (∑ i, e i) ≤ ∑ i, inner ℝ (b i) (A (H (b i)))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change lam * e i ≤ inner ℝ (b i) (A (H (b i)))
  rw [hHb, map_smul, real_inner_smul_right]
  have ha : lam ≤ inner ℝ (b i) (A (b i)) := by
    simpa only [b.orthonormal.norm_eq_one i, one_pow, mul_one] using hA (b i)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ha (he i)

/-- The non-divergence-form real elliptic operator, acting on the actual
gradient derivative. -/
def ellipticTrace (A : E → E →L[ℝ] E) (f : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E ((A x).comp (fderiv ℝ (gradient f) x)).toLinearMap

theorem laplacian_le_ellipticTrace_div_of_contact {K : Set E}
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (A : E → E →L[ℝ] E)
    {x : E} (hx : x ∈ lowerContactSet K f) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) :
    Laplacian.laplacian f x ≤ ellipticTrace A f x / lam := by
  have h := trace_comp_lower_of_positive (A x) (fderiv ℝ (gradient f) x)
    (fderiv_gradient_isPositive_of_contact hf hx) hA
  rw [trace_fderiv_gradient hf] at h
  exact (le_div_iff₀ hlam).mpr (by simpa only [ellipticTrace, mul_comm] using h)

end OAI.Analysis.PDE.Elliptic
