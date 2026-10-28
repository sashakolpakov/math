import OAI.Analysis.PDE.Schauder.Calculus.Interior.PathData
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.LogCoefficient

noncomputable section
open Set Module InnerProductSpace
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4

theorem InteriorThirdPathData.closed_coefficient_bounds
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 4 B₀) (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁)
    (x : E) (hx : r x ≤ 0) (v : E) :
    d.lower*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v) ∧
    inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v) ≤ d.upper*‖v‖^2 := by
  let f := fun x : E => inner ℝ v
    (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) v)
  have hcA : Continuous (fun x : E => OAI.Analysis.PDE.Dirichlet.detRealOperator
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x)) :=
    (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1).continuous.comp
      (OAI.Analysis.PDE.Dirichlet.continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ((hB₀.add s.smooth).of_le (by norm_num)))
  have hcf : Continuous f := continuous_const.inner (hcA.clm_apply continuous_const)
  have hi : interior {x | r x ≤ 0} ⊆ {x | d.lower*‖v‖^2 ≤ f x ∧ f x ≤ d.upper*‖v‖^2} := by
    intro y hy
    exact d.coefficient_bounds s y (OAI.Analysis.PDE.Dirichlet.neg_of_mem_interior_regular_sublevel hreg hy) v
  exact closure_minimal hi ((isClosed_le continuous_const hcf).inter (isClosed_le hcf continuous_const))
    (OAI.Analysis.PDE.Dirichlet.sublevel_subset_closure_interior hr hreg hx)

theorem path_equation_on_closed_sublevel
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ}
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) :
    ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) =
      OAI.Analysis.PDE.Dirichlet.densityPath F₀ F₁ s.t x := by
  exact OAI.Analysis.PDE.Dirichlet.equality_on_regular_sublevel_of_interior hr hreg
    (OAI.Analysis.PDE.Dirichlet.continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots ((hB₀.add s.smooth).of_le (by norm_num)))
    (OAI.Analysis.PDE.Dirichlet.contDiff_densityPath hF₀ hF₁ s.t).continuous
    (fun x hx => s.equation x (OAI.Analysis.PDE.Dirichlet.neg_of_mem_interior_regular_sublevel hreg hx))

theorem log_bounds_of_determinant_bounds
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {a b c C : ℝ} (ha : 0 < a) (_ : 0 < b) (hc : 0 ≤ c) (_ : 0 ≤ C)
    (hdet : a ≤ OAI.LinearAlgebra.Moore.mooreDet n A ∧ OAI.LinearAlgebra.Moore.mooreDet n A ≤ b)
    (hcoeff : ∀ v : E, c*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator A v) ∧
      inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator A v) ≤ C*‖v‖^2) (v : E) :
    (c/b)*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator A v) ∧
    inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator A v) ≤ (C/a)*‖v‖^2 := by
  have hd : 0 < OAI.LinearAlgebra.Moore.mooreDet n A := ha.trans_le hdet.1
  rw [OAI.Analysis.PDE.Dirichlet.logRealOperator_eq_smul_detRealOperator,smul_apply,real_inner_smul_right]
  constructor
  · calc
      (c/b)*‖v‖^2 = b⁻¹*(c*‖v‖^2) := by ring
      _ ≤ (OAI.LinearAlgebra.Moore.mooreDet n A)⁻¹*inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator A v) :=
        mul_le_mul (inv_anti₀ hd hdet.2) (hcoeff v).1 (by positivity) (by positivity)
  · calc
      (OAI.LinearAlgebra.Moore.mooreDet n A)⁻¹*inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator A v) ≤ a⁻¹*(C*‖v‖^2) :=
        mul_le_mul (inv_anti₀ ha hdet.1) (hcoeff v).2
          (le_trans (by positivity) (hcoeff v).1) (by positivity)
      _ = (C/a)*‖v‖^2 := by ring

end OAI.Analysis.PDE.Schauder
