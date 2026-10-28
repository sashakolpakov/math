import OAI.Analysis.PDE.Elliptic.Boundary.CurvedHolder
import OAI.Analysis.PDE.Elliptic.Boundary.FieldBounds

/-! Boundary Hölder control of a genuine tangent derivative of a solution
of the quaternionic Monge–Ampère equation. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology

def chartFieldNormal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (T F : E → E) (v z : E) : ℝ :=
  fderiv ℝ (fieldDerivative u T) (F z) (fderiv ℝ F z v)

theorem chartFieldNormal_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {T F : E → E} (hu : ContDiff ℝ 2 u) (hT : Differentiable ℝ T) (v z : E) :
    chartFieldNormal u T F v z =
      fderiv ℝ u (F z) (fderiv ℝ T (F z) (fderiv ℝ F z v)) +
      fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z v) (T (F z)) :=
  directionalDerivative_fieldDerivative hu hT _ _

theorem log_equation_boundary_field_holder {n : ℕ} [Nonempty (Fin n)]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ V : ℝ, 0 ≤ V →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), ‖v‖ = 1 →
      ∀ (P F T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
        (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ),
      ContDiff ℝ 3 u → ContDiff ℝ 2 T →
      (∀ z ∈ closedHalfBall v, ContDiffAt ℝ 2 F z) →
      (∀ z ∈ closedHalfBall v, DifferentiableAt ℝ P (F z)) →
      (∀ z ∈ closedHalfBall v, (fun y => P (F y)) =ᶠ[𝓝 z] id) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ V) →
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
      (∀ z, ‖z‖ ≤ 1 → inner ℝ v z = 0 → fieldDerivative u T (F z) = 0) →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        |chartFieldNormal u T F v z - chartFieldNormal u T F v z'| ≤ C * ‖z - z'‖ ^ α := by
  obtain ⟨α, hα, hα1, hholder⟩ := boundary_chart_normal_holder (ι := Fin n × Fin 4) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro V hV
  let d : ℝ := Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
  let W := max V (max (2 * V ^ 2) (V ^ 2 + d * V * (3 * V ^ 2)))
  have hVW : V ≤ W := le_max_left _ _
  have h2W : 2 * V ^ 2 ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have h3W : V ^ 2 + d * V * (3 * V ^ 2) ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨C, hC, hholder⟩ := hholder W (hV.trans hVW)
  refine ⟨C, hC, ?_⟩
  intro v hv P F T u f hu hT hF hP hinv hDu hD2u hT0 hT1 hT2 hF1 hF2 hA hB hlo hhi hf hf1 heq hzero
  have hfield : ContDiff ℝ 2 (fieldDerivative u T) := contDiff_fieldDerivative hu hT (by norm_num)
  apply hholder v hv (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) P F
    (fieldDerivative u T) hF (fun _ _ => hfield.contDiffAt) hP hinv _
    (fun z hz => (hF1 z hz).trans hVW) (fun z hz => (hF2 z hz).trans hVW)
    (fun z hz => (hB z hz).trans hVW) hlo hhi _ hzero
  · intro z hz
    apply (fderiv_fieldDerivative_bound (hu.of_le (by norm_num)) (hT.differentiable (by norm_num)) (F z)).trans
    apply le_trans _ h2W
    have h1 := mul_le_mul (hDu z hz) (hT1 z hz) (norm_nonneg _) hV
    have h2 := mul_le_mul (hD2u z hz) (hT0 z hz) (norm_nonneg _) hV
    nlinarith
  · intro z hz
    have hzc : z ∈ closedHalfBall v := ⟨hz.1.le, hz.2.le⟩
    apply (log_equation_fieldDerivative_bound hu hT (hf z hz) (heq z hz)).trans
    apply le_trans _ h3W
    have h0 : ‖fderiv ℝ f (F z)‖ * ‖T (F z)‖ / |f (F z)| ≤ V ^ 2 := by
      rw [mul_div_right_comm]
      have h := mul_le_mul (hf1 z hz) (hT0 z hzc) (norm_nonneg _) hV
      nlinarith
    have h1 : 2 * ‖fderiv ℝ (gradient u) (F z)‖ * ‖fderiv ℝ T (F z)‖ +
        ‖fderiv ℝ u (F z)‖ * ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ 3 * V ^ 2 := by
      have h := mul_le_mul (hD2u z hzc) (hT1 z hzc) (norm_nonneg _) hV
      have h' := mul_le_mul (hDu z hzc) (hT2 z hzc) (norm_nonneg _) hV
      nlinarith
    apply add_le_add h0
    change d * ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))‖ * _ ≤ _
    apply mul_le_mul (mul_le_mul_of_nonneg_left (hA z hzc) (Nat.cast_nonneg _)) h1
      (by positivity) (by positivity)

end OAI.Analysis.PDE.Elliptic
