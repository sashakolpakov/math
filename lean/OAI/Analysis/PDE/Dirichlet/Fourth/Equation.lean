import OAI.Analysis.PDE.Nonlinear.Fourth
import OAI.Analysis.PDE.Nonlinear.HolderComponents
import OAI.Analysis.PDE.Dirichlet.InitialDensity

/-! Exact differentiated equations used in the fourth-order bootstrap. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

local instance fourthEquationFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthEquationFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthEquationSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthEquationSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem directional_sum {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] (a : I → E → ℝ) (v x : E)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    directionalDerivative (fun y => ∑ i, a i y) v x =
      ∑ i, directionalDerivative (a i) v x := by
  unfold directionalDerivative
  have he : (fun y => ∑ i, a i y) = ∑ i, a i := by
    funext y
    simp only [Finset.sum_apply]
  rw [he]
  simpa only [Finset.sum_apply, sum_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_sum (u := Finset.univ) (fun i _ => ha i))

private theorem directional_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E → ℝ) (v x : E) (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    directionalDerivative (fun y => a y * b y) v x =
      a x * directionalDerivative b v x + directionalDerivative a v x * b x := by
  unfold directionalDerivative
  change (fderiv ℝ (a * b) x) v = _
  rw [fderiv_mul ha hb]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Differentiation of the actual coefficient-contracted Hessian. -/
theorem indexedNondivergence_directional {I : Type*} [Fintype I] [DecidableEq I]
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u : EuclideanSpace ℝ I → ℝ)
    (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u) (v x : EuclideanSpace ℝ I) :
    directionalDerivative (indexedNondivergenceOperator A u) v x =
      indexedNondivergenceOperator A (directionalDerivative u v) x +
      indexedNondivergenceOperator
        (fun y i j => directionalDerivative (fun z => A z i j) v y) u x := by
  have hentry (i j : I) : ContDiff ℝ 1 (fun y => A y i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i)) j
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have hh (i j : I) : ContDiff ℝ 1 (fun y => fderiv ℝ (fderiv ℝ u) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :=
    (hH.clm_apply contDiff_const).clm_apply contDiff_const
  unfold indexedNondivergenceOperator
  rw [directional_sum _ v x (fun i =>
    (ContDiff.sum (fun j _ => (hentry i j).mul (hh i j))).differentiable one_ne_zero x)]
  simp_rw [directional_sum _ v x (fun j =>
    ((hentry _ j).mul (hh _ j)).differentiable one_ne_zero x)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [directional_mul _ _ v x ((hentry i j).differentiable one_ne_zero x)
    ((hh i j).differentiable one_ne_zero x)]
  congr 1
  congr 1
  change fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x v = _
  rw [OAI.Analysis.Calculus.Quaternion.fderiv_second_apply hu.contDiffAt,
    OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu]

/-- The lower-order term in the second differentiated Moore equation.
It contains derivatives of the potential of order at most three. -/
def mooreSecondForcing {n : ℕ} (u f : CoordinateSpace n 4 → ℝ)
    (v w : CoordinateSpace n 4) (x : CoordinateSpace n 4) : ℝ :=
  directionalDerivative (directionalDerivative f v) w x -
    indexedNondivergenceOperator
      (fun y i j => directionalDerivative
        (fun z => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z) i j) w y)
      (directionalDerivative u v) x

theorem moore_second_directional_equation {n : ℕ}
    (u f : CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 4 u) (hf : ContDiff ℝ 2 f)
    (v w x : CoordinateSpace n 4)
    (hPDE : ∀ᶠ y in 𝓝 x, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) = f y) :
    indexedNondivergenceOperator
      (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (directionalDerivative (directionalDerivative u v) w) x =
        mooreSecondForcing u f v w x := by
  let A := fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)
  have hA : ContDiff ℝ 1 A :=
    (contDiff_mooreRealMatrix n 1).comp
      (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots (hu.of_le (by norm_num)))
  have hv : ContDiff ℝ 3 (directionalDerivative u v) :=
    contDiff_directionalDerivative hu (by norm_num) v
  have heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 x] f := hPDE
  have hfirst : indexedNondivergenceOperator A (directionalDerivative u v)
      =ᶠ[𝓝 x] directionalDerivative f v := by
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    rw [mooreRealMatrix_linearization_at _ (hv.of_le (by norm_num)).contDiffAt]
    exact mooreLinearization_directional_eq (hu.of_le (by norm_num)) v
      (hf.differentiable (by norm_num) y) hy
  have hdiff := congrArg (fun L : CoordinateSpace n 4 →L[ℝ] ℝ => L w)
    (hfirst.fderiv_eq (𝕜 := ℝ))
  change directionalDerivative (indexedNondivergenceOperator A (directionalDerivative u v)) w x =
    directionalDerivative (directionalDerivative f v) w x at hdiff
  rw [indexedNondivergence_directional A (directionalDerivative u v) hA hv w x] at hdiff
  exact eq_sub_of_add_eq hdiff

theorem contDiff_mooreSecondForcing {n : ℕ}
    (u f : CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 4 u) (hf : ContDiff ℝ 3 f)
    (v w : CoordinateSpace n 4) : ContDiff ℝ 1 (mooreSecondForcing u f v w) := by
  have hA : ContDiff ℝ 2 (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) :=
    (contDiff_mooreRealMatrix n 2).comp (contDiff_quaternionHessian_two OAI.Analysis.Calculus.Quaternion.fourSlots hu)
  have hv : ContDiff ℝ 3 (directionalDerivative u v) :=
    contDiff_directionalDerivative hu (by norm_num) v
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (directionalDerivative u v))) :=
    (hv.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have hfv : ContDiff ℝ 2 (directionalDerivative f v) :=
    contDiff_directionalDerivative hf (by norm_num) v
  apply (contDiff_directionalDerivative hfv (by norm_num) w).sub
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (contDiff_directionalDerivative
    (contDiff_pi.mp (contDiff_pi.mp hA i) j) (by norm_num) w).mul
      ((hH.clm_apply contDiff_const).clm_apply contDiff_const)

end OAI.Analysis.PDE.Dirichlet
