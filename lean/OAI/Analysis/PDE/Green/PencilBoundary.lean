import OAI.Analysis.PDE.Green.SecondGreenQuaternion
import OAI.Analysis.PDE.Dirichlet.Boundary.Hessian

/-! The common fiber/background null direction cancels every pencil's normal cofactor. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise

theorem quaternion_tensor_mulVec {n : ℕ} (p q v : Fin n → Quaternion ℝ) :
    (Matrix.of (fun i j => p i * star (q j))) *ᵥ v = fun i => p i * (star q ⬝ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_assoc, Finset.mul_sum, Pi.star_apply]

theorem quaternionHessian_add_mul {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (t : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x + t • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x := by
  simpa only [smul_eq_mul] using OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul e hB hu t x

theorem boundary_pencil_tangential_kernel {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (t : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hrne : fderiv ℝ r x ≠ 0) (hx : r x = 0)
    (huz : ∀ y, r y = 0 → u y = 0) (v : Fin n → Quaternion ℝ)
    (hRv : OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ v = 0)
    (hBv : OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ v = 0)
    (horth : star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ v = 0) :
    ∃ a : Quaternion ℝ, OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x *ᵥ v =
      fun i => OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x i * a := by
  have hz : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0 :=
    Filter.Eventually.of_forall (fun y hy => huz y (hy.trans hx))
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

/-- The normal cofactor vanishes for every real pencil parameter. The only
kernel input is the common null vector supplied by fiber geometry. -/
theorem boundary_pencil_normal_cofactor_zero {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (t : ℝ)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ v : Fin n → Quaternion ℝ, v ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ v = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ v = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ v = 0)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hx : r x = 0) :
    (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x))
      (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x)).re = 0 := by
  by_cases hd : fderiv ℝ r x = 0
  · have hg : OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x = 0 := by
      funext i
      simp [OAI.Analysis.PDE.Dirichlet.quaternionGradient, OAI.Analysis.Calculus.Quaternion.gradientMap, OAI.Analysis.PDE.Dirichlet.realGradient, hd]
    simp [hg, OAI.Analysis.PDE.Dirichlet.quaternionForm]
  obtain ⟨v, hv, hRv, hBv, horth⟩ := hcommon x hx
  obtain ⟨a, ha⟩ := boundary_pencil_tangential_kernel e hr hu hB t x hd hx huz v hRv hBv horth
  exact OAI.LinearAlgebra.Moore.mooreCofactor_normal_zero_of_tangential_kernel _
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e (hB.add (contDiff_const.mul hu)).contDiffAt)
    _ v hv horth a ha

/-- The Green identity for every member of the determinant pencil, proved
from shared fiber geometry and the actual zero boundary values of `u`. -/
theorem pencil_second_green {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) :
    (∫ x in {x | r x < 0}, u x * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in {x | r x < 0}, v x * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  exact moore_cofactor_second_green e (hB.add (contDiff_const.mul hu))
    (hu.of_le (by norm_num)) hv hr hb hrne huz
    (boundary_pencil_normal_cofactor_zero e hr (hu.of_le (by norm_num))
      (hB.of_le (by norm_num)) t huz hcommon)

end OAI.Analysis.PDE.Green
