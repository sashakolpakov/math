import OAI.Analysis.Calculus.Quaternion.CofactorDivergence
import OAI.Analysis.Calculus.Quaternion.CurrentOperations
import OAI.Analysis.PDE.Green.BoundedGreen
import OAI.Analysis.PDE.Green.CellCofactor

noncomputable section
open Set Matrix _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace OAI.LinearAlgebra.MixedDiscriminant

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

local instance rankMixedMatrixContinuousSMul (n : ℕ) :
    ContinuousSMul ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → Quaternion ℝ))

local instance rankMixedMatrixContinuousConstSMul (n : ℕ) :
    ContinuousConstSMul ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousConstSMul ℝ (Fin n → Fin n → Quaternion ℝ))

theorem fderiv_finset_smul_sum {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (t : Finset ι) (c : ι → ℝ) (A : ι → E → F) {x : E}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (A i) x) :
    fderiv ℝ (fun y => ∑ i ∈ t, c i • A i y) x =
      ∑ i ∈ t, c i • fderiv ℝ (A i) x := by
  have hs : fderiv ℝ (fun y => ∑ i ∈ t, c i • A i y) x =
      ∑ i ∈ t, fderiv ℝ (fun y => c i • A i y) x := by
    simpa only [Pi.smul_def] using
      (fderiv_fun_sum (fun i hi => (h i hi).const_smul (c i)))
  refine hs.trans (Finset.sum_congr rfl ?_)
  intro i hi
  simpa only [Pi.smul_def] using fderiv_const_smul (h i hi) (c i)

theorem contDiff_finset_smul_sum {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (t : Finset ι) (c : ι → ℝ) (A : ι → E → F)
    (h : ∀ i ∈ t, ContDiff ℝ 1 (A i)) :
    ContDiff ℝ 1 (fun y => ∑ i ∈ t, c i • A i y) := by
  apply ContDiff.sum
  intro i hi
  exact (h i hi).const_smul (c i)

theorem strongDivergence_finset_sum {n s : ℕ} {ι : Type*}
    (e : Fin s → Quaternion ℝ) (t : Finset ι)
    (A : ι → (Fin n × Fin s) → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => ∑ i ∈ t, A i p) b =
      ∑ i ∈ t, OAI.Analysis.Calculus.Quaternion.strongDivergence e (A i) b := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [OAI.Analysis.Calculus.Quaternion.strongDivergence]
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [OAI.Analysis.Calculus.Quaternion.strongDivergence_add,ih]

/-- Conservation is preserved by every finite real linear polarization. -/
theorem linear_combination_divergence {n s : ℕ} {ι : Type*}
    (e : Fin s → Quaternion ℝ) (t : Finset ι) (c : ι → ℝ)
    (A : ι → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : ∀ i ∈ t, ContDiff ℝ 1 (A i))
    (hdiv : ∀ i ∈ t, ∀ x b,
      OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ (A i) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ (fun y => ∑ i ∈ t, c i • A i y) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  have hs := fderiv_finset_smul_sum t c A
    (fun i hi => (hA i hi).differentiable one_ne_zero x)
  have hd : (fun p => fderiv ℝ (fun y => ∑ i ∈ t, c i • A i y) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) =
      (fun p => ∑ i ∈ t, c i • fderiv ℝ (A i) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) := by
    funext p
    simpa only [_root_.sum_apply,_root_.smul_apply] using!
      congrArg (fun L => L (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) hs
  rw [hd]
  rw [strongDivergence_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [OAI.Analysis.Calculus.Quaternion.strongDivergence_smul,hdiv i hi]
  simp

theorem linear_combination_cofactor_divergence {n s : ℕ} {ι : Type*}
    (e : Fin s → Quaternion ℝ) (t : Finset ι) (c : ι → ℝ)
    (ψ : ι → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hψ : ∀ i ∈ t, ContDiff ℝ 3 (ψ i))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ (fun y => ∑ i ∈ t,
        c i • OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) y)) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  apply linear_combination_divergence
  · intro i hi
    exact (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one e (hψ i hi))
  · intro i hi y j
    exact OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e (hψ i hi).contDiffAt j

end OAI.LinearAlgebra.MixedDiscriminant
