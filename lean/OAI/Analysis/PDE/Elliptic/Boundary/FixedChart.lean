import OAI.Analysis.PDE.Elliptic.Boundary.LocalHolder

/-! Uniform ellipticity in boundary coordinates is derived from the actual
inverse Jacobians. Only the original physical operator bounds are inputs. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem pullbackEllipticOperator_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (T A : E →L[ℝ] E) :
    ‖pullbackEllipticOperator T A‖ ≤ ‖T‖ ^ 2 * ‖A‖ := by
  simpa only [hessianCongruence, pullbackEllipticOperator, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint.norm_map] using hessianCongruence_norm T.adjoint A

theorem log_equation_boundary_fixed_chart_holder {n : ℕ} [Nonempty (Fin n)]
    {lam V C0 : ℝ} (hlam : 0 < lam) (hV : 0 < V) (hC0 : 0 < C0)
    (P G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hP : ContDiff ℝ 3 P) (hG : ContDiff ℝ 3 G) (hB : ContDiff ℝ 3 B)
    (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hv : ‖v‖ = 1)
    (hinv : ∀ z ∈ closedHalfBall v, (fun y => P (G y)) =ᶠ[𝓝 z] id)
    (hP1 : ∀ z ∈ closedHalfBall v, ‖fderiv ℝ P (G z)‖ ≤ C0)
    (hG1 : ∀ z ∈ closedHalfBall v, ‖fderiv ℝ G z‖ ≤ C0)
    (hG2 : ∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 G z‖ ≤ C0)
    (hG3 : ∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 3 G z‖ ≤ C0) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ), ContDiff ℝ 3 u → Continuous f →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))).PosDef) →
      (∀ z ∈ closedHalfBall v, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)) w)) →
      (∀ z ∈ closedHalfBall v, DifferentiableAt ℝ f (G z)) →
      (∀ z ∈ closedHalfBall v, f (G z) ≠ 0) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ f (G z)‖ / |f (G z)| ≤ V) →
      (∀ z ∈ openHalfBall v,
        (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (G z)] f) →
      (∀ z, ‖z‖ ≤ 2 → inner ℝ v z = 0 → u (G z) = B (G z)) →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ ≤ C * ‖z - z'‖ ^ α := by
  let W := V + C0 + C0 ^ 2 * V + 1
  have hW : 0 < W := by dsimp [W]; positivity
  have hCV : 0 ≤ C0 ^ 2 * V := mul_nonneg (sq_nonneg C0) hV.le
  have hVW : V ≤ W := by dsimp [W]; linarith
  have hCW : C0 ≤ W := by dsimp [W]; linarith
  have hC2W : C0 ^ 2 * V ≤ W := by dsimp [W]; linarith
  obtain ⟨α, C, hα, hα1, hC, hholder⟩ := log_equation_boundary_chart_holder
    (div_pos hlam (sq_pos_of_pos hC0)) (mul_pos hV (sq_pos_of_pos hC0)) hlam hW P G B hP hG hB
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro u f hu hf hDu hD2u hpos hA hlo hdf hfne hf1 heq hzero
  have hupper (z) (hz : z ∈ closedHalfBall v) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :
      inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)) w) ≤ V * ‖w‖ ^ 2 := by
    apply (real_inner_le_norm _ _).trans
    have hh := (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))).le_opNorm w
    have hh' := hh.trans (mul_le_mul_of_nonneg_right (hA z hz) (norm_nonneg w))
    nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg w)]
  have hb (z) (hz : z ∈ closedHalfBall v) := pullbackEllipticOperator_bounds_of_inverse
    (fderiv ℝ P (G z)) (fderiv ℝ G z) (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)))
    hC0 hlam.le hV.le
    (chart_jacobians_inverse (hP.differentiable (by norm_num) (G z))
      (hG.differentiable (by norm_num) z) (hinv z hz)).1
    (hP1 z hz) (hG1 z hz) (hlo z hz) (hupper z hz)
  have hnorm (z) (hz : z ∈ closedHalfBall v) :
      ‖pullbackEllipticOperator (fderiv ℝ P (G z))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)))‖ ≤ W := by
    apply (pullbackEllipticOperator_norm_bound _ _).trans
    apply le_trans _ hC2W
    exact mul_le_mul (by nlinarith [norm_nonneg (fderiv ℝ P (G z)), hP1 z hz])
      (hA z hz) (norm_nonneg _) (sq_nonneg C0)
  exact hholder v hv hinv (fun z hz => (hP1 z hz).trans hCW)
    (fun z hz => (hG1 z hz).trans hCW) (fun z hz => (hG2 z hz).trans hCW)
    (fun z hz => (hG3 z hz).trans hCW) u f hu hf
    (fun z hz => (hDu z hz).trans hVW) (fun z hz => (hD2u z hz).trans hVW) hpos
    (fun z hz => (hA z hz).trans hVW) hnorm hlo
    (fun z hz w => (hb z hz w).1) (fun z hz w => (hb z hz w).2)
    hdf hfne (fun z hz => (hf1 z hz).trans hVW) heq hzero

end OAI.Analysis.PDE.Elliptic
