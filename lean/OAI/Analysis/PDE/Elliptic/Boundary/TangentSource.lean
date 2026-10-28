import OAI.Analysis.PDE.Elliptic.Boundary.Chart.DriftSource
import OAI.Analysis.PDE.Elliptic.Boundary.VectorFieldLocal

/-! A genuine C^α source for the differentiated nonlinear chart equation.
All solution-dependent source bounds use only the original C²,α norm. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

theorem exists_log_chart_tangent_source {n : ℕ}
    {Ω K S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hconv : Convex ℝ S) {G P : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (he : ‖e‖ ≤ 1)
    (A J B : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α)
    (C D : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S)
      (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α) (Q : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hA : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A ⟨x, subset_closure hx⟩ = OAI.Analysis.PDE.Dirichlet.logRealOperator
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) (G x)))
    (hJ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ (chartTangentField G P e) (G x))
    (hC : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value C x =
      fderiv ℝ (fderiv ℝ (chartTangentField G P e)) (G x))
    (hB : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ G x)
    (hD : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ (fderiv ℝ G) x)
    (hV : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V ⟨x, subset_closure hx⟩ = inverseChartDrift
      (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) z)) G P x)
    (hQ : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x, subset_closure hx⟩ =
      fderiv ℝ f (G x) (fderiv ℝ G x e) / f (G x))
    (hu : ∀ x ∈ S, ContDiffAt ℝ 3 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) (G x))
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f (G x))
    (hinv : ∀ x ∈ S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    (heq : ∀ x ∈ S,
      (fun z => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
        (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) z)) =ᶠ[𝓝 (G x)] f) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α,
      (∀ x, ∀ hx : x ∈ S, ellipticTrace
        (fun z => pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) (G z))))
        (fun z => fderiv ℝ (fun y => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G y)) z e) x =
          OAI.Analysis.Normed.Function.Holder.HolderMap.value R ⟨x, subset_closure hx⟩) ∧
      ‖R‖ ≤ ‖Q‖ + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) *
        (8 * (max 1 (L^α) * ‖U‖) * ‖A‖ * ‖J‖ + 4 * (max 1 L * ‖U‖) * ‖A‖ * ‖C‖) +
        (8 * (max 1 (L^α) * ‖U‖) * ‖B‖^2 * ‖V‖ + 4 * (max 1 L * ‖U‖) * ‖D‖ * ‖V‖) := by
  obtain ⟨R₁, hR₁, hn₁⟩ := exists_chart_commutator_holder_interior U hΩ hS hconv
    (hG.of_le (by norm_num)) hGK hGΩ hL hDG hα hα1 hdiam A J C
      (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) z))
      (chartTangentField G P e) hA hJ hC
  obtain ⟨R₂, hR₂, hn₂⟩ := exists_chart_directional_drift_holder_interior U hΩ hS hconv
    (hG.of_le (by norm_num)) hGK hGΩ hL hDG hα hα1 hdiam B D V
    (inverseChartDrift (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) z)) G P) hB hD hV he
  refine ⟨Q + R₁ + R₂, ?_, ?_⟩
  · intro x hx
    have hh := log_equation_chart_tangent hG hP e x (hu x hx) (hf x hx) (hinv x hx) (heq x hx)
    dsimp only at hh
    change _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x, subset_closure hx⟩ +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value R₁ ⟨x, subset_closure hx⟩ + OAI.Analysis.Normed.Function.Holder.HolderMap.value R₂ ⟨x, subset_closure hx⟩
    rw [hQ x hx, hR₁ x hx, hR₂ x hx]
    exact hh
  · exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hn₁)) hn₂)

end OAI.Analysis.PDE.Elliptic
