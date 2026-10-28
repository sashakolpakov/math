import OAI.LinearAlgebra.MixedDiscriminant.GreenLinear
import OAI.LinearAlgebra.Moore.Rank.Mixed.Cofactor

noncomputable section
open Set Matrix _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace OAI.LinearAlgebra.MixedDiscriminant

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

local instance mixedHessianContinuousConstSMul (n : ℕ) :
    ContinuousConstSMul ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousConstSMul ℝ (Fin n → Fin n → Quaternion ℝ))

theorem quaternionHessian_finset_sum {n s : ℕ} {ι : Type*}
    (e : Fin s → Quaternion ℝ) (t : Finset ι)
    (ψ : ι → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hψ : ∀ i ∈ t, ContDiff ℝ 2 (ψ i))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => ∑ i ∈ t, ψ i y) x =
      ∑ i ∈ t, OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hz : OAI.Analysis.PDE.Dirichlet.realHessian (fun _ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s => (0 : ℝ)) x = 0 := by
        ext p q
        simp [OAI.Analysis.PDE.Dirichlet.realHessian]
      simp only [Finset.sum_empty,OAI.Analysis.PDE.Dirichlet.quaternionHessian,hz]
      exact (OAI.Analysis.Calculus.Quaternion.hessianCLM e).map_zero
  | @insert a t ha ih =>
      have h1 := hψ a (Finset.mem_insert_self a t)
      have ht : ∀ i ∈ t, ContDiff ℝ 2 (ψ i) := fun i hi =>
        hψ i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert ha]
      have hadd := OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul e h1 (ContDiff.sum ht) 1 x
      simp only [one_smul] at hadd
      rw [hadd,ih ht]

/-- The finite polarization of Hessian cofactors is an actual finite sum of
ordinary cofactors of summed potentials. -/
theorem mixedCofactor_hessian_eq_sum {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (ψ : Fin (n - 1) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hψ : ∀ i, ContDiff ℝ 3 (ψ i)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x) =
      ∑ t : Finset (Fin (n - 1)),
        (((n - 1).factorial : ℝ)⁻¹ * (-1 : ℝ) ^ (n - 1 - t.card)) •
          OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => ∑ i ∈ t, ψ i y) x) := by
  rw [OAI.LinearAlgebra.Moore.mixedCofactor_eq_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [quaternionHessian_finset_sum e t ψ
    (fun i _ => (hψ i).of_le (by norm_num))]
  exact (mul_smul _ _ _).symm

theorem contDiff_mixedCofactor_hessian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (ψ : Fin (n - 1) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hψ : ∀ i, ContDiff ℝ 3 (ψ i)) :
    ContDiff ℝ 1 (fun x => OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x)) := by
  simp_rw [mixedCofactor_hessian_eq_sum e ψ hψ]
  apply contDiff_finset_smul_sum
  intro t ht
  exact (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp
    (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one e (ContDiff.sum (fun i _ => hψ i)))

/-- Mixed Hessian cofactors are divergence-free; no conservation hypothesis
is imposed on the polarized field. -/
theorem mixedCofactor_hessian_divergence {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (ψ : Fin (n - 1) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hψ : ∀ i, ContDiff ℝ 3 (ψ i)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ
        (fun y => OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) y)) x
          (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  simp_rw [mixedCofactor_hessian_eq_sum e ψ hψ]
  exact linear_combination_cofactor_divergence e Finset.univ
    (fun t : Finset (Fin (n - 1)) =>
      ((n - 1).factorial : ℝ)⁻¹ * (-1 : ℝ) ^ (n - 1 - t.card))
    (fun t y => ∑ i ∈ t, ψ i y)
    (fun t _ => ContDiff.sum (fun i _ => hψ i)) x b

end OAI.LinearAlgebra.MixedDiscriminant
