import OAI.Analysis.PDE.Dirichlet.Uniform.Interior

/-! Uniform pairwise interior Hölder control on a neighborhood, formulated
for the same physical Hessian as the closed-boundary estimate. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem interior_hessian_holder_near_point {n : ℕ}
    {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)} (hΩ : IsOpen Ω)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) (hx : x ∈ Ω)
    {lam L L₁ L₂ V : ℝ} (hlam : 0 < lam) (hL : lam ≤ L)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hV : 0 ≤ V) :
    ∃ ρ a C : ℝ, 0 < ρ ∧ 0 < a ∧ a < 1 ∧ 0 < C ∧
      ∀ ψ F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 ψ →
      (∀ y ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)).PosDef) →
      (∀ y ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) = F y) →
      (∀ y ∈ Ω, ∀ v, lam * ‖v‖ ^ 2 ≤ OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) v ∧
        OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) v ≤ L * ‖v‖ ^ 2) →
      (∀ y ∈ Ω, ‖fderiv ℝ (gradient ψ) y‖ ≤ V) →
      (∀ y ∈ Ω, ∀ z ∈ Ω, |Real.log (F y) - Real.log (F z)| ≤ L₁ * dist y z) →
      (∀ y ∈ Ω, ∀ v, -L₂ * ‖v‖ ^ 2 ≤
        deriv (deriv (fun t : ℝ => Real.log (F (y + t • v)))) 0) →
      ∀ y ∈ closedBall x ρ, ∀ z ∈ closedBall x ρ,
        ‖fderiv ℝ (gradient ψ) y - fderiv ℝ (gradient ψ) z‖ ≤ C * dist y z ^ a := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  obtain ⟨a, C, ha, ha1, hC, hholder⟩ := OAI.Analysis.PDE.Dirichlet.log_equation_uniform_interior_ball
    hlam hL hL₁ hL₂ hV (half_pos hε)
  refine ⟨ε / 8, a, C, by positivity, ha, ha1, hC, ?_⟩
  intro ψ F hψ hpos heq hell hnorm hlog hlog₂ y hy z hz
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  by_cases hyz : y = z
  · subst z
    simp [Real.zero_rpow ha.ne']
  have hd : 0 < dist y z := dist_pos.mpr hyz
  have hdist : dist y z ≤ ε / 2 := by
    have ht := dist_triangle y x z
    have hy' : dist y x ≤ ε / 8 := hy
    have hz' : dist z x ≤ ε / 8 := hz
    rw [dist_comm x z] at ht
    linarith
  have hsub : closedBall y (ε / 2) ⊆ Ω := by
    intro w hw
    apply hball
    have hw' : dist w y ≤ ε / 2 := hw
    have hy' : dist y x ≤ ε / 8 := hy
    have ht := dist_triangle w y x
    change dist w x < ε
    linarith
  have ht := hholder ψ F y hψ
    (fun w hw => hpos w (hsub hw)) (fun w hw => heq w (hsub hw))
    (fun w hw => hell w (hsub hw))
    (fun w hw => by simpa only [norm_fderiv_gradient hψ2] using hnorm w (hsub hw))
    (fun w hw v hv => hlog w (hsub hw) v (hsub hv))
    (fun w hw => hlog₂ w (hsub (ball_subset_closedBall hw)))
    (dist y z) hd hdist y (by simp [hd.le]) z (by simp [dist_comm])
  rwa [← norm_fderiv_gradient_sub hψ2] at ht

end OAI.Analysis.PDE.Elliptic
