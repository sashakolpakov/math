import OAI.Analysis.PDE.Elliptic.Boundary.LogFieldHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Expansion
import OAI.Analysis.PDE.Elliptic.Boundary.FieldRemainder

/-! Boundary Hölder estimate with the prescribed background explicitly subtracted. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology

theorem log_equation_boundary_remainder_expansion {n : ℕ} [Nonempty (Fin n)]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ V : ℝ, 0 ≤ V →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), ‖v‖ = 1 →
      ∀ (P F T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
        (u B f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ),
      ContDiff ℝ 3 u → ContDiff ℝ 3 B → ContDiff ℝ 2 T →
      (∀ z ∈ closedHalfBall v, ContDiffAt ℝ 2 F z) →
      (∀ z ∈ closedHalfBall v, DifferentiableAt ℝ P (F z)) →
      (∀ z ∈ closedHalfBall v, (fun y => P (F y)) =ᶠ[𝓝 z] id) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (fieldDerivative B T) (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient (fieldDerivative B T)) (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ F z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 F z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖pullbackEllipticOperator (fderiv ℝ P (F z))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z)))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (F z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))) w)) →
      (∀ z ∈ closedHalfBall v, ∀ w, inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (F z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))) w) ≤ L * ‖w‖ ^ 2) →
      (∀ z ∈ openHalfBall v, DifferentiableAt ℝ f (F z)) →
      (∀ z ∈ openHalfBall v, ‖fderiv ℝ f (F z)‖ / |f (F z)| ≤ V) →
      (∀ z ∈ openHalfBall v,
        (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (F z)] f) →
      (∀ z, ‖z‖ ≤ 1 → inner ℝ v z = 0 → fieldDerivative (fun y => u y - B y) T (F z) = 0) →
      ∀ z, ‖z‖ ≤ 1 / 4 → inner ℝ v z = 0 →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, ‖x - z‖ ≤ r / 2 → 0 ≤ inner ℝ v x →
        |fieldDerivative (fun y => u y - B y) T (F x) -
          chartFieldNormal (fun y => u y - B y) T F v z * inner ℝ v x| ≤
            C * r ^ α * inner ℝ v x := by
  obtain ⟨α, hα, hα1, hholder⟩ := boundary_chart_first_order_expansion (ι := Fin n × Fin 4) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro V hV
  let d : ℝ := Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
  let W := max V (max (2 * V ^ 2 + V) (V ^ 2 + d * V * (3 * V ^ 2 + V)))
  have hVW : V ≤ W := le_max_left _ _
  have h2W : 2 * V ^ 2 + V ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have h3W : V ^ 2 + d * V * (3 * V ^ 2 + V) ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨C, hC, hholder⟩ := hholder W (hV.trans hVW)
  refine ⟨C, hC, ?_⟩
  intro v hv P F T u B f hu hB hT hF hP hinv hDu hD2u hT0 hT1 hT2 hBack1 hBack2 hF1 hF2 hA hBB hlo hhi hf hf1 heq hzero
  have hfield : ContDiff ℝ 2 (fieldDerivative (fun y => u y - B y) T) :=
    contDiff_fieldDerivative (hu.sub hB) hT (by norm_num)
  apply hholder v hv (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) P F
    (fieldDerivative (fun y => u y - B y) T) hF (fun _ _ => hfield.contDiffAt) hP hinv _
    (fun z hz => (hF1 z hz).trans hVW) (fun z hz => (hF2 z hz).trans hVW)
    (fun z hz => (hBB z hz).trans hVW) hlo hhi _ hzero
  · intro z hz
    apply (field_remainder_fderiv_bound hu hB hT (F z)).trans
    apply le_trans _ h2W
    have h1 := mul_le_mul (hDu z hz) (hT1 z hz) (norm_nonneg _) hV
    have h2 := mul_le_mul (hD2u z hz) (hT0 z hz) (norm_nonneg _) hV
    have h3 := hBack1 z hz
    nlinarith
  · intro z hz
    have hzc : z ∈ closedHalfBall v := ⟨hz.1.le, hz.2.le⟩
    apply (log_equation_field_remainder_bound hu hB hT (hf z hz) (heq z hz)).trans
    apply le_trans _ h3W
    have h0 : ‖fderiv ℝ f (F z)‖ * ‖T (F z)‖ / |f (F z)| ≤ V ^ 2 := by
      rw [mul_div_right_comm]
      have h := mul_le_mul (hf1 z hz) (hT0 z hzc) (norm_nonneg _) hV
      nlinarith
    have h1 : 2 * ‖fderiv ℝ (gradient u) (F z)‖ * ‖fderiv ℝ T (F z)‖ +
        ‖fderiv ℝ u (F z)‖ * ‖iteratedFDeriv ℝ 2 T (F z)‖ +
        ‖fderiv ℝ (gradient (fieldDerivative B T)) (F z)‖ ≤ 3 * V ^ 2 + V := by
      have h := mul_le_mul (hD2u z hzc) (hT1 z hzc) (norm_nonneg _) hV
      have h' := mul_le_mul (hDu z hzc) (hT2 z hzc) (norm_nonneg _) hV
      have h'' := hBack2 z hzc
      nlinarith
    apply add_le_add h0
    change d * ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))‖ * _ ≤ _
    apply mul_le_mul (mul_le_mul_of_nonneg_left (hA z hzc) (Nat.cast_nonneg _)) h1
      (by positivity) (by positivity)

end OAI.Analysis.PDE.Elliptic
