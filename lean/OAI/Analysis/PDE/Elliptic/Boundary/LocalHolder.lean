import OAI.Analysis.PDE.Elliptic.Boundary.Density
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants

/-! The actual nonlinear equation implies full boundary C²,α control in a
fixed C³ chart.  No mixed, normal, or log-density estimate is assumed. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem log_equation_boundary_chart_holder {n : ℕ} [Nonempty (Fin n)]
    {lam L mu V : ℝ} (hlam : 0 < lam) (hL : 0 < L) (hmu : 0 < mu) (hV : 0 < V)
    (P G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hP : ContDiff ℝ 3 P) (hG : ContDiff ℝ 3 G) (hB : ContDiff ℝ 3 B) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), ‖v‖ = 1 →
      (∀ z ∈ closedHalfBall v, (fun y => P (G y)) =ᶠ[𝓝 z] id) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ P (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ G z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 G z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 3 G z‖ ≤ V) →
      ∀ (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ), ContDiff ℝ 3 u → Continuous f →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))).PosDef) →
      (∀ z ∈ closedHalfBall v, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖pullbackEllipticOperator (fderiv ℝ P (G z))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ∀ w, mu * ‖w‖ ^ 2 ≤ inner ℝ w
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)) w)) →
      (∀ z ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))) w)) →
      (∀ z ∈ closedHalfBall v, ∀ w, inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))) w) ≤ L * ‖w‖ ^ 2) →
      (∀ z ∈ closedHalfBall v, DifferentiableAt ℝ f (G z)) →
      (∀ z ∈ closedHalfBall v, f (G z) ≠ 0) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ f (G z)‖ / |f (G z)| ≤ V) →
      (∀ z ∈ openHalfBall v,
        (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (G z)] f) →
      (∀ z, ‖z‖ ≤ 2 → inner ℝ v z = 0 → u (G z) = B (G z)) →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ ≤ C * ‖z - z'‖ ^ α := by
  obtain ⟨α, hα, hα1, hmixed⟩ := log_equation_chart_mixed_holder (n := n) hlam hL
  obtain ⟨M, hM, hmixed⟩ := hmixed P G B hP hG hB V hV.le
  obtain ⟨K, hK, hback⟩ := exists_compact_hessian_lipschitz
    (B := fun y => B (G y)) (hB.comp hG) (isCompact_closedBall (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) 1)
    (convex_closedBall _ _)
  let R := 3 * V ^ 5 + V ^ 4 + V ^ 2 * (4 * M + K)
  let C := V ^ 2 * ((V ^ 2 + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * V * R) / (mu / V ^ 2)) + R
  have hR : 0 < R := by dsimp [R]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro v hv hinv hP1 hG1 hG2 hG3 u f hu hf hDu hD2u hpos hA hAA hraw hlo hhi hdf hfne hf1 heq hzero
  have hopen (y) (hy : y ∈ openHalfBall v) : y ∈ closedHalfBall v := ⟨hy.1.le, hy.2.le⟩
  have hm := hmixed v hv hinv u f hu hDu hD2u hA hAA hlo hhi
    (fun y hy => hdf y (hopen y hy)) (fun y hy => hf1 y (hopen y hy)) heq hzero
  intro z z' hz hz' hvz hvz'
  have hzc : z ∈ closedHalfBall v := ⟨by linarith, hvz.ge⟩
  have hz'c : z' ∈ closedHalfBall v := ⟨by linarith, hvz'.ge⟩
  have hJ := chart_jacobians_inverse (hP.differentiable (by norm_num) (G z))
    (hG.differentiable (by norm_num) z) (hinv z hzc)
  have hlog := log_density_chart_lipschitz (convex_closedHalfBall v) hdf
    (fun y _ => hG.differentiable (by norm_num) y) hfne hV.le hV.le hf1 hG1 hzc hz'c
  have heqpoint (y) (hy : ‖y‖ < 1) (hvy : inner ℝ v y = 0) :
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G y)) = f (G y) :=
    moore_equation_chart_boundary (hu.of_le (by norm_num)) hf hG.continuous hv hy hvy
      (fun a ha => (heq a ha).eq_of_nhds)
  have hlog' : |Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z')))| ≤ V ^ 2 * ‖z - z'‖ := by
    rw [heqpoint z (by linarith) hvz, heqpoint z' (by linarith) hvz']
    simpa only [pow_two] using hlog
  exact chart_hessian_holder_from_mixed (hu.of_le (by norm_num)) (hB.of_le (by norm_num)) hG
    hv hV hmu hα1.le hM.le hK.le (sq_nonneg V) hz hz' hvz hvz' hDu hD2u hG1 hG2 hG3
    (fderiv ℝ P (G z)) (hP1 z hzc) hJ.2 hJ.1
    (fun y hy hyv => hzero y (by linarith) hyv)
    (fun e he hve => hm e he hve z z' hz hz' hvz hvz')
    (hback z (by simpa using hzc.1) z' (by simpa using hz'c.1))
    (hpos z hzc) (hpos z' hz'c) (hraw z hzc) (hraw z' hz'c) (hA z hzc) (hA z' hz'c) hlog'

end OAI.Analysis.PDE.Elliptic
