import OAI.Analysis.PDE.Green.PencilBoundary
import OAI.Analysis.PDE.Green.Localized.Green

/-! Pointwise boundary cancellation needs zero Dirichlet data only locally.
This permits compact time tests and an arbitrary extension away from them. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise

theorem secondGreenFlux_tangent_local
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Fintype I]
    (d : I → E) (K : I → I → E → ℝ) {r u v : E → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) (x : E) (hx : r x = 0)
    (huz : ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0)
    (hnormal : (∑ i, ∑ j, K i j x *
      (fderiv ℝ r x (d i) * fderiv ℝ r x (d j))) = 0) :
    (∑ i, fderiv ℝ r x (d i) * secondGreenFlux d K u v i x) = 0 := by
  by_cases hd : fderiv ℝ r x = 0
  · simp only [hd, _root_.zero_apply, zero_mul, Finset.sum_const_zero]
  have hz : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0 :=
    huz.mono (fun y hy hyr => hy (hyr.trans hx))
  obtain ⟨a, ha⟩ := OAI.Analysis.PDE.Dirichlet.level_set_gradient_factor
    (hr.hasStrictFDerivAt (by norm_num)) hd (hu.differentiable (by norm_num) x) hz
  have hux : u x = 0 := huz.self_of_nhds hx
  have hflux (i : I) : secondGreenFlux d K u v i x =
      -v x * (∑ j, K i j x * (a * fderiv ℝ r x (d j))) := by
    unfold secondGreenFlux
    rw [hux, zero_mul, zero_sub]
    simp only [realFlux, ha, _root_.smul_apply, smul_eq_mul]
    ring
  calc
    _ = -(v x * a) * (∑ i, ∑ j, K i j x *
        (fderiv ℝ r x (d i) * fderiv ℝ r x (d j))) := by
      simp only [hflux, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hnormal]; ring

theorem boundary_pencil_tangential_kernel_local {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (t : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hrne : fderiv ℝ r x ≠ 0) (hx : r x = 0)
    (huz : ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0) (v : Fin n → Quaternion ℝ)
    (hRv : OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ v = 0)
    (hBv : OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ v = 0)
    (horth : star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ v = 0) :
    ∃ a : Quaternion ℝ, OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x *ᵥ v =
      fun i => OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x i * a := by
  have hz : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0 :=
    huz.mono (fun y hy hyr => hy (hyr.trans hx))
  obtain ⟨a, ha⟩ := OAI.Analysis.PDE.Dirichlet.level_set_gradient_factor (hr.hasStrictFDerivAt (by norm_num))
    hrne (hu.differentiable (by norm_num) x) hz
  obtain ⟨l, hl⟩ := OAI.Analysis.PDE.Dirichlet.boundary_quaternionHessian_decomposition e hr hu hrne hz ha
  refine ⟨t • (star l ⬝ᵥ v), ?_⟩
  rw [quaternionHessian_add_mul e hB hu t x, hl]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, hBv, hRv,
    quaternion_tensor_mulVec, horth, mul_zero, smul_zero, zero_add]
  funext i
  change t • (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x i * (star l ⬝ᵥ v) + 0) =
    OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x i * (t • (star l ⬝ᵥ v))
  rw [add_zero]
  exact (mul_smul_comm t (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x i) (star l ⬝ᵥ v)).symm

theorem boundary_pencil_normal_cofactor_zero_local {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (t : ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hx : r x = 0)
    (huz : ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0)
    (hcommon : ∃ v : Fin n → Quaternion ℝ, v ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ v = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ v = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ v = 0) :
    (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x))
      (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x)).re = 0 := by
  by_cases hd : fderiv ℝ r x = 0
  · have hg : OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x = 0 := by
      funext i
      simp [OAI.Analysis.PDE.Dirichlet.quaternionGradient, OAI.Analysis.Calculus.Quaternion.gradientMap, OAI.Analysis.PDE.Dirichlet.realGradient, hd]
    simp [hg, OAI.Analysis.PDE.Dirichlet.quaternionForm]
  obtain ⟨v, hv, hRv, hBv, horth⟩ := hcommon
  obtain ⟨a, ha⟩ := boundary_pencil_tangential_kernel_local e hr hu hB t x hd hx huz v hRv hBv horth
  exact OAI.LinearAlgebra.Moore.mooreCofactor_normal_zero_of_tangential_kernel _
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e (hB.add (contDiff_const.mul hu)).contDiffAt)
    _ v hv horth a ha

end OAI.Analysis.PDE.Green
