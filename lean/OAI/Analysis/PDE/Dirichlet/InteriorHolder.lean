import OAI.Analysis.PDE.Dirichlet.EllipticEquations
import OAI.Analysis.PDE.Elliptic.FrameRecovery
import OAI.Analysis.PDE.Elliptic.Evans.SystemHolder

open Set Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- Interior Evans–Krylov estimate for the actual quaternionic equation.
The hypotheses on the density are bounds for its first and second logarithmic
derivatives; the solution hypotheses are the previously proved C² and uniform
ellipticity bounds. No regularity theorem is supplied as an assumption. -/
theorem log_equation_interior_holder {n : ℕ} {lam L L₁ L₂ V : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hV : 0 ≤ V) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ (ψ F : CoordinateSpace (n + 1) 4 → ℝ) (z : CoordinateSpace (n + 1) 4),
      ContDiff ℝ 4 ψ →
      (∀ x ∈ closedBall z 1, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ closedBall z 1, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ closedBall z 1, ∀ v,
        lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ closedBall z 1, ‖fderiv ℝ (gradient ψ) x‖ ≤ V) →
      (∀ x ∈ closedBall z 1, ∀ y ∈ closedBall z 1,
        |Real.log (F x) - Real.log (F y)| ≤ L₁ * dist x y) →
      (∀ x ∈ ball z 1, ∀ v,
        -L₂ * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0) →
      ∀ r, 0 < r → r ≤ 1 → ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
        ‖fderiv ℝ (gradient ψ) x - fderiv ℝ (gradient ψ) y‖ ≤ B * r ^ α := by
  classical
  let E := CoordinateSpace (n + 1) 4
  let I := Fin (Module.finrank ℝ E)
  let : Nonempty I := ⟨⟨0, Module.finrank_pos (R := ℝ) (M := E)⟩⟩
  obtain ⟨bs, hbs, δ, C, hδ, hC, hdecomp⟩ :=
    OAI.Analysis.PDE.Elliptic.uniform_signed_frame_decomposition (E := E) hlam hL
  obtain ⟨b₀, hb₀⟩ := hbs
  let : Nonempty {b // b ∈ bs} := ⟨⟨b₀, hb₀⟩⟩
  let J := {b // b ∈ bs} × OAI.Analysis.PDE.Elliptic.SignedFrameIndex I
  let v : J → E := fun j ↦ OAI.Analysis.PDE.Elliptic.signedFrame j.1.val j.2
  let D : ℝ := 1 + ∑ j, ‖v j‖ ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hvD (j : J) : ‖v j‖ ^ 2 ≤ D := by
    have hs := Finset.single_le_sum (s := (Finset.univ : Finset J))
      (f := fun i ↦ ‖v i‖ ^ 2) (fun i _ ↦ sq_nonneg ‖v i‖) (Finset.mem_univ j)
    dsimp [D]
    linarith
  let d : ℝ := Fintype.card (Fin (n + 1) × Fin 4)
  have hd : 0 < d := by dsimp [d]; positivity
  let K := L₂ * D / (2 * lam * d)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKscale : 2 * K * lam * d = L₂ * D := by
    dsimp [K]
    field_simp
  obtain ⟨α, B, hα, hα1, hB, hholder⟩ := OAI.Analysis.PDE.Elliptic.elliptic_system_holder_oscillation
    (ι := Fin (n + 1) × Fin 4) (J := J) hlam (hlam.trans_le hL) hδ hC hL₁ hK
    (show 0 ≤ 2 * (V * D) * (Fintype.card J : ℝ) by positivity)
  refine ⟨α, B, hα, hα1, hB, ?_⟩
  intro ψ F z hψ hpos heq hell hnorm hlog hlog₂
  let A : E → E →L[ℝ] E := fun x ↦ logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
  let w : J → E → ℝ := fun j ↦ directionalDerivative (directionalDerivative ψ (v j)) (v j)
  have hψ₂ : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hw (j : J) : ContDiff ℝ 2 (w j) := by
    have hv3 : ContDiff ℝ 3 (directionalDerivative ψ (v j)) :=
      contDiff_directionalDerivative hψ (by norm_num) (v j)
    exact contDiff_directionalDerivative hv3 (by norm_num) (v j)
  have hwval (j : J) (x : E) : w j x = inner ℝ (v j) (fderiv ℝ (gradient ψ) x (v j)) := by
    rw [show w j x = directionalDerivative (directionalDerivative ψ (v j)) (v j) x from rfl,
      directionalDerivative_twice hψ₂]
    exact (OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient hψ₂ x (v j) (v j)).symm.trans (real_inner_comm _ _)
  have hlow (x : E) (hx : x ∈ closedBall z 1) (u : E) :
      lam * ‖u‖ ^ 2 ≤ inner ℝ u (A x u) := by
    rw [show A x = logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) from rfl,
      logRealOperator_symbol]
    exact (hell x hx u).1
  have hupp (x : E) (hx : x ∈ closedBall z 1) (u : E) :
      inner ℝ u (A x u) ≤ L * ‖u‖ ^ 2 := by
    rw [show A x = logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) from rfl,
      logRealOperator_symbol]
    exact (hell x hx u).2
  have hsource (j : J) (x : E) (hx : x ∈ ball z 1) :
      -(2 * K * lam * Fintype.card (Fin (n + 1) × Fin 4)) ≤ OAI.Analysis.PDE.Elliptic.ellipticTrace A (w j) x := by
    have hpde := log_equation_second_directional_ge hψ isOpen_ball
      (fun x hx ↦ hpos x (ball_subset_closedBall hx))
      (fun x hx ↦ heq x (ball_subset_closedBall hx)) (v j) hx
    have hl := hlog₂ x hx (v j)
    have hm := mul_le_mul_of_nonneg_left (hvD j) hL₂
    change -(2 * K * lam * d) ≤ _
    rw [hKscale]
    exact (by linarith : -(L₂ * D) ≤
      deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v j)))) 0).trans hpde
  have hcoupled (x : E) (hx : x ∈ closedBall z 1) (y : E) (hy : y ∈ closedBall z 1) :
      ∃ a : J → ℝ, (∀ j, δ ≤ a j ∧ a j ≤ C) ∧
        -(L₁ * dist x y) ≤ ∑ j, a j * (w j x - w j y) := by
    obtain ⟨c, hc, hrep⟩ := hdecomp (A y)
      (logRealOperator_isSymmetric _) (hlow y hy) (hupp y hy)
    let a : J → ℝ := fun j ↦ c j.1 j.2
    have hr : logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) =
        ∑ j, a j • rankOne ℝ (v j) (v j) := by
      change logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) =
        ∑ j : {b // b ∈ bs} × OAI.Analysis.PDE.Elliptic.SignedFrameIndex I,
          c j.1 j.2 • rankOne ℝ (OAI.Analysis.PDE.Elliptic.signedFrame j.1.val j.2) (OAI.Analysis.PDE.Elliptic.signedFrame j.1.val j.2)
      simpa only [A, Fintype.sum_prod_type] using hrep
    have hxy := log_equation_weighted_difference hψ₂ x y (hpos x hx) (hpos y hy)
      (heq x hx) (heq y hy) v a hr
    exact ⟨a, fun j ↦ hc j.1 j.2, (abs_le.mp (hlog x hx y hy)).1.trans hxy⟩
  have hwbound (j : J) (x : E) (hx : x ∈ closedBall z 1) : |w j x| ≤ V * D := by
    rw [hwval]
    have hvnorm := (fderiv ℝ (gradient ψ) x).le_opNorm (v j)
    have hvx := hnorm x hx
    calc
      _ ≤ ‖v j‖ * ‖fderiv ℝ (gradient ψ) x (v j)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v j‖ * (V * ‖v j‖) := mul_le_mul_of_nonneg_left
        (hvnorm.trans (mul_le_mul_of_nonneg_right hvx (norm_nonneg _))) (norm_nonneg _)
      _ = V * ‖v j‖ ^ 2 := by ring
      _ ≤ V * D := mul_le_mul_of_nonneg_left (hvD j) hV
  have hstart := OAI.Analysis.PDE.Elliptic.familyOscillation_le_of_abs_le (fun j ↦ (hw j).continuous) z
    (by norm_num : (0 : ℝ) ≤ 1) hwbound
  have hosc := hholder z A w hw hlow hupp hsource hcoupled hstart
  intro r hr hr1 x hx y hy
  let H := fderiv ℝ (gradient ψ) x - fderiv ℝ (gradient ψ) y
  have hH : H.toLinearMap.IsSymmetric := by
    intro u v
    change inner ℝ ((fderiv ℝ (gradient ψ) x - fderiv ℝ (gradient ψ) y) u) v =
      inner ℝ u ((fderiv ℝ (gradient ψ) x - fderiv ℝ (gradient ψ) y) v)
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    exact congrArg₂ (fun a b : ℝ ↦ a - b)
      (OAI.Analysis.PDE.Elliptic.fderiv_gradient_isSymmetric hψ₂ x u v) (OAI.Analysis.PDE.Elliptic.fderiv_gradient_isSymmetric hψ₂ y u v)
  have hrecovery := OAI.Analysis.PDE.Elliptic.norm_le_familyFrame_quadratics bs ⟨b₀, hb₀⟩ H hH
  have hsum : (∑ j : J, |inner ℝ (v j) (H (v j))|) ≤ OAI.Analysis.PDE.Elliptic.familyOscillation w z r := by
    apply Finset.sum_le_sum
    intro j _
    have he : inner ℝ (v j) (H (v j)) = w j x - w j y := by
      simp only [H, sub_apply, inner_sub_right, hwval]
    rw [he]
    exact OAI.Analysis.PDE.Elliptic.abs_sub_le_ball_oscillation (hw j).continuous hx hy
  exact hrecovery.trans (hsum.trans (hosc r hr hr1))

end OAI.Analysis.PDE.Dirichlet
