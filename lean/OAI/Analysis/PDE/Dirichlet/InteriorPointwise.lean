import OAI.Analysis.PDE.Dirichlet.InteriorPointwiseFields
import OAI.Analysis.PDE.Schauder.Calculus.Interior.LocalJet
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniformInterior

open Set Metric InnerProductSpace
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance interiorPointwiseFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance interiorPointwiseFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance interiorPointwiseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorPointwiseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The physical interior estimate for an actual elliptic-trace equation.
All coefficient and forcing bounds are restricted to K. The radius is
fixed before the small error, and the constant before the solution. -/
theorem interior_pointwise_schauder (hm : 3 ≤ m)
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α ell Λ N ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (x₀ : E) (hball : closedBall x₀ ρ ⊆ K) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : E → E →L[ℝ] E,
      (∀ x ∈ K, (A x).toLinearMap.IsSymmetric) →
      (∀ x ∈ K, ‖A x‖ ≤ N) →
      (∀ x ∈ K, ∀ y ∈ K, ‖A x-A y‖ ≤ N*‖x-y‖^α) →
      (∀ z, ell*‖z‖^2 ≤ inner ℝ z (A x₀ z)) →
      (∀ z, inner ℝ z (A x₀ z) ≤ Λ*‖z‖^2) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u → ∀ F : E → ℝ,
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      ∀ B M, 0 ≤ B → 0 ≤ M →
      (∀ x ∈ K, ‖u x‖ ≤ M) →
      (∀ x ∈ K, ‖F x‖ ≤ B) →
      (∀ x ∈ K, ∀ y ∈ K, ‖F x-F y‖ ≤ B*‖x-y‖^α) →
      (∀ x ∈ K, OAI.Analysis.PDE.Elliptic.ellipticTrace A u x = F x) →
      (∀ x ∈ closedBall x₀ δ,
        ‖u x‖ ≤ ε*‖U‖+D*(B+M) ∧
        ‖fderiv ℝ u x‖ ≤ ε*‖U‖+D*(B+M) ∧
        ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε*‖U‖+D*(B+M)) ∧
      (∀ x ∈ closedBall x₀ δ, ∀ y ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤
          (ε*‖U‖+D*(B+M))*‖x-y‖^α) := by
  let k : Fin m := ⟨0, by omega⟩
  obtain ⟨C, hC, hcut⟩ := exists_uniform_interior_normalized_cutoff_hessian_bound
    (hΩK := hΩK) hα.le hα1.le (Real.sqrt_nonneg Λ)
  obtain ⟨r, hr, hrone, hrnear, hrnear₂, δ, hδ, hlocal⟩ :=
    OAI.Analysis.PDE.Schauder.uniform_interior_local_jet_schauder hm k hα hα1 hell hΛ hN hρ
  refine ⟨δ/2, half_pos hδ, ?_⟩
  intro ε hε
  let ε' := ε/(C+1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal ε' hε'
  let D := D₀+1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro A hAs hAn hAh hlower hupper u hu F U hU₀ hU₁ hU₂ B M hB hM hub hFn hFh heq
  have h₀K : x₀ ∈ K := hball (mem_closedBall_self hρ.le)
  obtain ⟨A', hA', hA'n⟩ := exists_closedBall_matrix_field x₀ hρ.le hα hN A
    (fun x hx => hAn x (hball hx))
    (fun x hx y hy => hAh x (hball hx) y (hball hy))
  have hpd : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A' x₀).PosDef := by
    rw [hA' x₀ (mem_closedBall_self hρ.le)]
    apply OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix_posDef _ (hAs _ h₀K)
    intro z hz
    rw [real_inner_comm]
    exact lt_of_lt_of_le (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hz))) (hlower z)
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A' x₀) = A x₀ := by
    rw [hA' x₀ (mem_closedBall_self hρ.le)]
    exact OAI.Analysis.PDE.Schauder.toEuclideanCLM_euclideanCoefficientMatrix _ (hAs _ h₀K)
  obtain ⟨L, hL, hLi, hLestimate⟩ := hestimate A' hA'n x₀ hpd
    (by simpa only [hclm] using hlower) (by simpa only [hclm] using hupper)
  obtain ⟨F', hF', hF'n⟩ := exists_closedBall_holder_field x₀ hρ.le hα hB F
    (fun x hx => hFn x (hball hx))
    (fun x hx y hy => hFh x (hball hx) y (hball hy))
  have hscale : 2*r*Real.sqrt Λ < ρ := by
    have hh := (lt_div_iff₀ (by positivity)).mp hrnear₂
    nlinarith
  have himage : MapsTo (fun z => x₀+L (r • z)) (closedBall 0 2) K :=
    (normalized_affine_mapsTo_ball L.toContinuousLinearMap x₀ hr.le
      (Real.sqrt_nonneg Λ) hL hscale).mono_right (ball_subset_closedBall.trans hball)
  have houter := (hcut L.toContinuousLinearMap x₀ r hL hr hrone himage
    u (hu.of_le (by norm_num)) U hU₀ hU₁ hU₂).2
  have hactual (x : E) (hx : x ∈ ball x₀ ρ) :
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F' x := by
    have hxclosed := ball_subset_closedBall hx
    have hxK := hball hxclosed
    rw [hF' x hxclosed]
    have hm : OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') u x =
        OAI.Analysis.PDE.Schauder.nondivergenceOperator (fun y => OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (A y)) u x := by
      apply OAI.Analysis.PDE.Schauder.nondivergenceOperator_congr_at
      exact hA' x hxclosed
    rw [hm, ← OAI.Analysis.PDE.Schauder.ellipticTrace_eq_nondivergenceOperator A u (hu.of_le (by norm_num)) x (hAs _ hxK)]
    exact heq x hxK
  obtain ⟨hjets, hholder⟩ := hLestimate u hu F' (C*‖U‖) M (by positivity) hM
    (fun x hx => by simpa only [Real.norm_eq_abs] using hub x (hball (ball_subset_closedBall hx)))
    hactual houter
  have hbudget : ε'*(C*‖U‖)+D₀*(‖F'‖+M) ≤ ε*‖U‖+D*(B+M) := by
    have hs : ε'*C ≤ ε := by
      dsimp only [ε']
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have herr := mul_le_mul_of_nonneg_right hs (norm_nonneg U)
    have hforce : D₀*(‖F'‖+M) ≤ D*(B+M) := by
      have hD₀D : D₀ ≤ D := by dsimp only [D]; linarith
      exact mul_le_mul hD₀D (by linarith) (by positivity) hD.le
    nlinarith
  have hvalue : M ≤ ε*‖U‖+D*(B+M) := by
    have hD1 : 1 ≤ D := by dsimp only [D]; linarith
    have hb := mul_le_mul_of_nonneg_right hD1 (add_nonneg hB hM)
    nlinarith [mul_nonneg hε.le (norm_nonneg U)]
  have hsmall (x : E) (hx : x ∈ closedBall x₀ (δ/2)) : x ∈ ball x₀ δ :=
    lt_of_le_of_lt hx (half_lt_self hδ)
  constructor
  · intro x hx
    obtain ⟨h₀,h₁,h₂⟩ := hjets x (hsmall x hx)
    exact ⟨(by simpa only [Real.norm_eq_abs] using h₀.trans hvalue), h₁.trans hbudget, h₂.trans hbudget⟩
  · intro x hx y hy
    exact (hholder x (hsmall x hx) y (hsmall y hy)).trans
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Dirichlet
