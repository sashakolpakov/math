import OAI.Analysis.PDE.Energy.Rank.Energy.Moments
import OAI.LinearAlgebra.Moore.Rank.Mixed.Positive
import OAI.LinearAlgebra.Moore.Rank.Mixed.Growth

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem mixed_hessian_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hB : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hD : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef)
    (j : ℕ) : 0 ≤ OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
      if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x) := by
  apply OAI.LinearAlgebra.Moore.mixedMoore_nonneg
  intro i
  split
  · exact hB
  · exact hD

theorem mixedHessianMass_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : MeasurableSet S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hneg : ∀ x ∈ S, u x ≤ 0)
    (hB : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hD : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef)
    (j : ℕ) : 0 ≤ mixedHessianMass e S B u j := by
  apply setIntegral_nonneg hS
  intro x hx
  exact mul_nonneg (neg_nonneg.mpr (hneg x hx)) (mixed_hessian_nonneg e (hB x hx) (hD x hx) j)

theorem mixedHessianMass_eq_zero_of_rank {n s r j : ℕ}
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : MeasurableSet S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hD : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef)
    (hrank : ∀ x ∈ S, OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x))
    (hrj : r < j) (hjn : j ≤ n) : mixedHessianMass e S B u j = 0 := by
  unfold mixedHessianMass
  calc
    (∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
      if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)) = ∫ _x in S, (0 : ℝ) := by
      apply setIntegral_congr_fun hS
      intro x hx
      dsimp only
      rw [OAI.LinearAlgebra.Moore.mixedMoore_eq_zero_of_rank_and_nonneg _ _ (hB x hx) (hD x hx)
        (hrank x hx) hrj hjn (fun k _ => mixed_hessian_nonneg e (hB x hx) (hD x hx) k)]
      exact mul_zero _
    _ = 0 := integral_zero _ _

end OAI.Analysis.PDE.Energy
