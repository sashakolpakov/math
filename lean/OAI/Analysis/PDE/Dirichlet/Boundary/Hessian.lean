import OAI.Analysis.PDE.Dirichlet.LevelSet

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A symmetric bilinear form vanishing on a hyperplane has only normal cross terms. -/
theorem bilinear_hyperplane_decomposition (H : E →L[ℝ] E →L[ℝ] ℝ)
    (g : E →L[ℝ] ℝ) (hg : g ≠ 0)
    (hsymm : ∀ v w, H v w = H w v)
    (htan : ∀ v w, g v = 0 → g w = 0 → H v w = 0) :
    ∃ l : E →L[ℝ] ℝ, ∀ v w, H v w = g v * l w + l v * g w := by
  obtain ⟨e₀, he₀⟩ := linear_form_exists_negative g hg
  let e := (g e₀)⁻¹ • e₀
  have he : g e = 1 := by simp [e, he₀.ne]
  refine ⟨H e - (H e e / 2) • g, ?_⟩
  intro v w
  have h := htan (v - g v • e) (w - g w • e) (by simp [he]) (by simp [he])
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at h ⊢
  rw [hsymm e v]
  nlinarith [h]

/-- The exact second-order boundary identity. The unknown normal derivative
is confined to a pair of normal cross terms. -/
theorem boundary_hessian_decomposition [CompleteSpace E]
    {r u : E → ℝ} {x : E} {a : ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) (hrne : fderiv ℝ r x ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x) :
    ∃ l : E →L[ℝ] ℝ, ∀ v w,
      fderiv ℝ (fderiv ℝ u) x v w = a * fderiv ℝ (fderiv ℝ r) x v w +
        fderiv ℝ r x v * l w + l v * fderiv ℝ r x w := by
  let H := fderiv ℝ (fderiv ℝ u) x - a • fderiv ℝ (fderiv ℝ r) x
  have hs : ∀ v w, H v w = H w v := by
    intro v w
    simp only [H, sub_apply, smul_apply, smul_eq_mul]
    rw [(hu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w,
      (hr.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w]
  have ht : ∀ v w, fderiv ℝ r x v = 0 → fderiv ℝ r x w = 0 → H v w = 0 := by
    intro v w hv hw
    simp only [H, sub_apply, smul_apply, smul_eq_mul]
    rw [level_set_tangent_hessian hr hu hrne hzero hfactor hv hw]
    ring
  obtain ⟨l, hl⟩ := bilinear_hyperplane_decomposition H (fderiv ℝ r x) hrne hs ht
  refine ⟨l, fun v w ↦ ?_⟩
  have h := hl v w
  simp only [H, sub_apply, smul_apply, smul_eq_mul] at h
  linarith

end Normed

theorem boundary_realHessian_decomposition {n s : ℕ}
    {r u : CoordinateSpace n s → ℝ} {x : CoordinateSpace n s} {a : ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) (hrne : fderiv ℝ r x ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x) :
    ∃ l : Fin n × Fin s → ℝ, realHessian u x = a • realHessian r x +
      Matrix.of (fun i j ↦ realGradient r x i * l j) +
      Matrix.of (fun i j ↦ l i * realGradient r x j) := by
  obtain ⟨l, hl⟩ := boundary_hessian_decomposition hr hu hrne hzero hfactor
  refine ⟨fun i ↦ l (coordinateVector i), ?_⟩
  ext i j
  exact hl (coordinateVector i) (coordinateVector j)

theorem boundary_quaternionHessian_decomposition {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u : CoordinateSpace n s → ℝ} {x : CoordinateSpace n s} {a : ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) (hrne : fderiv ℝ r x ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x) :
    ∃ l : Fin n → Quaternion ℝ, quaternionHessian e u x = a • quaternionHessian e r x +
      Matrix.of (fun i j ↦ quaternionGradient e r x i * star (l j)) +
      Matrix.of (fun i j ↦ l i * star (quaternionGradient e r x j)) := by
  obtain ⟨l, hl⟩ := boundary_realHessian_decomposition hr hu hrne hzero hfactor
  refine ⟨OAI.Analysis.Calculus.Quaternion.gradientMap e l, ?_⟩
  simp only [quaternionHessian, quaternionGradient, hl, OAI.Analysis.Calculus.Quaternion.hessianMap_add,
    OAI.Analysis.Calculus.Quaternion.hessianMap_smul, OAI.Analysis.Calculus.Quaternion.hessianMap_tensor]

theorem quaternionForm_smul_matrix {n : ℕ} (a : ℝ)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (z : Fin n → Quaternion ℝ) :
    quaternionForm (a • A) z = a • quaternionForm A z := by
  simp [quaternionForm, Finset.smul_sum]

theorem quaternionForm_tensor {n : ℕ} (g l z : Fin n → Quaternion ℝ) :
    quaternionForm (Matrix.of (fun i j ↦ g i * star (l j))) z =
      (∑ i, star (z i) * g i) * (∑ j, star (l j) * z j) := by
  simp only [quaternionForm, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The normal cross terms disappear exactly on the quaternionic tangent space. -/
theorem boundary_quaternionHessian_tangent {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u : CoordinateSpace n s → ℝ} {x : CoordinateSpace n s} {a : ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) (hrne : fderiv ℝ r x ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x)
    (z : Fin n → Quaternion ℝ)
    (hz : ∑ i, star (quaternionGradient e r x i) * z i = 0) :
    quaternionForm (quaternionHessian e u x) z =
      a • quaternionForm (quaternionHessian e r x) z := by
  obtain ⟨l, hl⟩ := boundary_quaternionHessian_decomposition e hr hu hrne hzero hfactor
  have hz' : ∑ i, star (z i) * quaternionGradient e r x i = 0 := by
    simpa only [star_sum, star_mul, star_star, star_zero] using congrArg star hz
  rw [hl, quaternionForm_add, quaternionForm_add, quaternionForm_smul_matrix,
    quaternionForm_tensor, quaternionForm_tensor, hz', hz]
  simp

end OAI.Analysis.PDE.Dirichlet
