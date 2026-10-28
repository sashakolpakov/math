import OAI.Analysis.PDE.Dirichlet.SchauderIsometry
import OAI.Analysis.PDE.Elliptic.Boundary.Pullback

open Set InnerProductSpace
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Contravariant transport of a coefficient by a constant isometry. -/
def isometryConjugate (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) : E →L[ℝ] E :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp e.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem isometryConjugate_apply (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) (v : E) :
    isometryConjugate e A v = e.symm (A (e v)) := rfl

theorem norm_isometryConjugate_le (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) :
    ‖isometryConjugate e A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa only [isometryConjugate_apply, e.symm.norm_map, e.norm_map] using A.le_opNorm (e v)

@[simp] theorem isometryConjugate_symm (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) :
    isometryConjugate e.symm (isometryConjugate e A) = A := by
  ext v
  simp only [isometryConjugate_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem norm_isometryConjugate (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) :
    ‖isometryConjugate e A‖ = ‖A‖ := by
  apply le_antisymm (norm_isometryConjugate_le e A)
  simpa only [isometryConjugate_symm] using norm_isometryConjugate_le e.symm (isometryConjugate e A)

@[simp] theorem isometryConjugate_sub (e : E ≃ₗᵢ[ℝ] F) (A B : F →L[ℝ] F) :
    isometryConjugate e (A - B) = isometryConjugate e A - isometryConjugate e B := by
  ext v
  simp only [isometryConjugate_apply, sub_apply, map_sub]

theorem inner_isometryConjugate (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) (v w : E) :
    inner ℝ (isometryConjugate e A v) w = inner ℝ (A (e v)) (e w) := by
  rw [← e.inner_map_map]
  simp only [isometryConjugate_apply, LinearIsometryEquiv.apply_symm_apply]

theorem isometryConjugate_isSymmetric (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F)
    (hA : A.toLinearMap.IsSymmetric) : (isometryConjugate e A).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (isometryConjugate e A v) w = inner ℝ v (isometryConjugate e A w)
  have hr : inner ℝ v (isometryConjugate e A w) = inner ℝ (e v) (A (e w)) := by
    rw [← e.inner_map_map]
    simp only [isometryConjugate_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [inner_isometryConjugate, hr]
  exact hA (e v) (e w)

theorem continuous_isometryConjugate_field (e : E ≃ₗᵢ[ℝ] F)
    (A : F → F →L[ℝ] F) (hA : Continuous A) :
    Continuous (fun x ↦ isometryConjugate e (A (e x))) := by
  exact continuous_const.clm_comp ((hA.comp e.continuous).clm_comp continuous_const)

theorem contDiff_isometryConjugate_field (e : E ≃ₗᵢ[ℝ] F)
    (A : F → F →L[ℝ] F) {k : WithTop ℕ∞} (hA : ContDiff ℝ k A) :
    ContDiff ℝ k (fun x ↦ isometryConjugate e (A (e x))) := by
  exact contDiff_const.clm_comp ((hA.comp e.contDiff).clm_comp contDiff_const)

theorem isometryConjugate_elliptic (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) {lam : ℝ}
    (hA : ∀ v : F, lam * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (v : E) :
    lam * ‖v‖ ^ 2 ≤ inner ℝ (isometryConjugate e A v) v := by
  rw [inner_isometryConjugate]
  simpa only [e.norm_map] using hA (e v)

theorem isometryConjugate_holder (e : E ≃ₗᵢ[ℝ] F) (A : F → F →L[ℝ] F)
    {K : Set F} {M α : ℝ}
    (hA : ∀ x ∈ K, ∀ y ∈ K, ‖A x - A y‖ ≤ M * dist x y ^ α)
    {x y : E} (hx : x ∈ e ⁻¹' K) (hy : y ∈ e ⁻¹' K) :
    ‖isometryConjugate e (A (e x)) - isometryConjugate e (A (e y))‖ ≤
      M * dist x y ^ α := by
  rw [← isometryConjugate_sub, norm_isometryConjugate]
  simpa only [e.isometry.dist_eq] using hA (e x) hx (e y) hy

section FiniteDimensional
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The genuine Hessian operator transforms by the same isometric conjugation. -/
theorem hessianOperator_isometry_pullback (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 2 u) (x : E) :
    fderiv ℝ (gradient (u ∘ e)) x =
      isometryConjugate e (fderiv ℝ (gradient u) (e x)) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [inner_isometryConjugate]
  rw [OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient_at (hu.comp e.contDiff).contDiffAt,
    OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient_at hu.contDiffAt]
  exact second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap x v w

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem isometryConjugate_comp (e : E ≃ₗᵢ[ℝ] F) (A B : F →L[ℝ] F) :
    (isometryConjugate e A).comp (isometryConjugate e B) = isometryConjugate e (A.comp B) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, isometryConjugate_apply,
    LinearIsometryEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem trace_isometryConjugate (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) :
    LinearMap.trace ℝ E (isometryConjugate e A).toLinearMap =
      LinearMap.trace ℝ F A.toLinearMap := by
  change LinearMap.trace ℝ E (e.symm.toLinearEquiv.conj A.toLinearMap) = _
  exact LinearMap.trace_conj' _ _

/-- Exact transport of the actual nondivergence elliptic equation. -/
theorem ellipticTrace_isometry_pullback (e : E ≃ₗᵢ[ℝ] F) (A : F → F →L[ℝ] F)
    (u : F → ℝ) (hu : ContDiff ℝ 2 u) (x : E) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y ↦ isometryConjugate e (A (e y))) (u ∘ e) x =
      OAI.Analysis.PDE.Elliptic.ellipticTrace A u (e x) := by
  unfold OAI.Analysis.PDE.Elliptic.ellipticTrace
  rw [hessianOperator_isometry_pullback e u hu, isometryConjugate_comp,
    trace_isometryConjugate]

end FiniteDimensional
end OAI.Analysis.PDE.Dirichlet
