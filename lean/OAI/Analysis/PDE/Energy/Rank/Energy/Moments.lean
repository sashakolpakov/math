import OAI.LinearAlgebra.Moore.Rank.Mixed.Continuity
import OAI.Analysis.PDE.Energy.Rank.Energy.Upper

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set _root_.MeasureTheory Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

def mixedHessianMass {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (j : ℕ) : ℝ :=
  ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
    if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
    else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)

theorem continuous_mixed_hessian_integrand {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (j : ℕ) : Continuous (fun x => (-u x) * OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
      if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) := by
  apply hu.continuous.neg.mul
  apply (OAI.LinearAlgebra.Moore.continuous_mixedMoore n).comp
  apply continuous_pi
  intro i
  by_cases h : i.val < j
  · simpa only [ite_eq_left h] using continuous_quaternionHessian_three e hB
  · simpa only [ite_eq_right h] using continuous_quaternionHessian_three e (hB.add hu)

theorem integrable_mixed_hessian_integrand {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (j : ℕ) : IntegrableOn (fun x => (-u x) * OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
      if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) S :=
  continuous_integrableOn_bounded hb (continuous_mixed_hessian_integrand e hB hu j)

@[simp] theorem mixedHessianMass_zero {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) :
    mixedHessianMass e S B u 0 = determinantMass e S (fun y => B y+u y) u := by
  simp only [mixedHessianMass, Nat.not_lt_zero, ite_false, OAI.LinearAlgebra.Moore.mixedMoore_const, determinantMass]

theorem integral_mixed_hessian_sum {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (J : Finset ℕ) (c : ℝ) :
    (∫ x in S, u x * (c * ∑ j ∈ J, OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
      if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x))) =
      -c * ∑ j ∈ J, mixedHessianMass e S B u j := by
  have he : (∫ x in S, u x * (c * ∑ j ∈ J, OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
      if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x))) =
      ∫ x in S, -c * ∑ j ∈ J, (-u x) * OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n =>
        if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
        else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) := by
    apply setIntegral_congr_fun hS
    intro x hx
    dsimp only
    rw [← Finset.mul_sum]
    ring
  rw [he, integral_const_mul,
    integral_finsetSum J (fun j _ => integrable_mixed_hessian_integrand e hb hB hu j)]
  rfl

theorem sum_mixedHessianMass_truncate {n s r : ℕ} (hr : r ≤ n)
    (e : Fin s → Quaternion ℝ) (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hzero : ∀ j, r < j → j ≤ n → mixedHessianMass e S B u j = 0) :
    (∑ j ∈ Finset.range (n+1), mixedHessianMass e S B u j) =
      ∑ j ∈ Finset.range (r+1), mixedHessianMass e S B u j := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr))
  intro j hj hjr
  apply hzero j
  · have : ¬ j < r+1 := by simpa only [Finset.mem_range] using hjr
    omega
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

end OAI.Analysis.PDE.Energy
