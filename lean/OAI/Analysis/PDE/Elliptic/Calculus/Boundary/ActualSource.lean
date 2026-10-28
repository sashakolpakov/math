import OAI.Analysis.PDE.Elliptic.Boundary.TangentSource
import OAI.Analysis.PDE.Elliptic.Boundary.TraceHolder

/-! The differentiated chart equation for the actual potential, rather
than an arbitrary extension of its stored jet. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

theorem chart_remainder_source {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} {α : ℝ} (hα : 0 ≤ α) (A : E → E →L[ℝ] E)
    (G : E → E) (f g : E → ℝ) (hf : ContDiff ℝ 3 f)
    (hg : ContDiff ℝ 3 g) (hG : ContDiff ℝ 3 G) (v : E)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α) (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (ha : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = A x)
    (hH : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (g ∘ G) v)) x)
    (x : S) (heq : ellipticTrace A (OAI.Analysis.PDE.Dirichlet.directionalDerivative (f ∘ G) v) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) :
    ellipticTrace A (OAI.Analysis.PDE.Dirichlet.directionalDerivative ((fun y => f y-g y) ∘ G) v) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (R-holderEllipticTrace hα a H) x := by
  have he : OAI.Analysis.PDE.Dirichlet.directionalDerivative ((fun y => f y-g y) ∘ G) v =
      fun y => OAI.Analysis.PDE.Dirichlet.directionalDerivative (f ∘ G) v y-OAI.Analysis.PDE.Dirichlet.directionalDerivative (g ∘ G) v y := by
    funext y
    exact congrArg (fun L : E →L[ℝ] ℝ => L v)
      (fderiv_sub ((hf.comp hG).differentiable (by norm_num) y)
        ((hg.comp hG).differentiable (by norm_num) y))
  have hdf : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative (f ∘ G) v) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative (hf.comp hG) (by norm_num) v
  have hdg : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative (g ∘ G) v) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative (hg.comp hG) (by norm_num) v
  rw [he, ellipticTrace_sub_at _ hdf.contDiffAt hdg.contDiffAt, heq]
  change _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x-OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderEllipticTrace hα a H) x
  rw [ellipticTrace_eq_hessian_sum _ hdg.contDiffAt,value_holderEllipticTrace]
  simp only [ha,hH]

theorem actual_value_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hΩ : IsOpen Ω) (u : E → ℝ)
    (hU : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) {x : E} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) =ᶠ[𝓝 x] u := by
  filter_upwards [hΩ.mem_nhds hx] with y hy
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK hy), hU]

theorem exists_actual_log_chart_tangent_source {n : ℕ}
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
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 3 u)
    (hU : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x)
    (hA : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A ⟨x, subset_closure hx⟩ =
      OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G x)))
    (hJ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ (chartTangentField G P e) (G x))
    (hC : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value C x =
      fderiv ℝ (fderiv ℝ (chartTangentField G P e)) (G x))
    (hB : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ G x)
    (hD : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ (fderiv ℝ G) x)
    (hV : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V ⟨x, subset_closure hx⟩ = inverseChartDrift
      (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) G P x)
    (hQ : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x, subset_closure hx⟩ =
      fderiv ℝ f (G x) (fderiv ℝ G x e) / f (G x))
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f (G x))
    (hinv : ∀ x ∈ S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    (heq : ∀ x ∈ S,
      (fun z => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) =ᶠ[𝓝 (G x)] f) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α,
      (∀ x, ∀ hx : x ∈ S, ellipticTrace
        (fun z => pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))))
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ G) e) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R ⟨x, subset_closure hx⟩) ∧
      ‖R‖ ≤ ‖Q‖ + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) *
        (8 * (max 1 (L^α) * ‖U‖) * ‖A‖ * ‖J‖ + 4 * (max 1 L * ‖U‖) * ‖A‖ * ‖C‖) +
        (8 * (max 1 (L^α) * ‖U‖) * ‖B‖^2 * ‖V‖ + 4 * (max 1 L * ‖U‖) * ‖D‖ * ‖V‖) := by
  obtain ⟨R₁,hR₁,hn₁⟩ := exists_chart_commutator_holder_interior U hΩ hS hconv
    (hG.of_le (by norm_num)) hGK hGΩ hL hDG hα hα1 hdiam A J C
    (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z))
    (chartTangentField G P e) hA hJ hC
  obtain ⟨R₂,hR₂,hn₂⟩ := exists_chart_directional_drift_holder_interior U hΩ hS hconv
    (hG.of_le (by norm_num)) hGK hGΩ hL hDG hα hα1 hdiam B D V
    (inverseChartDrift (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) G P) hB hD hV he
  refine ⟨Q+R₁+R₂, ?_, ?_⟩
  · intro x hx
    have hw := actual_value_germ U hΩ u hU (hGΩ hx)
    have hc : (fun y => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G y)) =ᶠ[𝓝 x] u ∘ G :=
      hG.continuous.continuousAt.tendsto.eventually hw
    have hd : (fun z => fderiv ℝ (fun y => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G y)) z e)
        =ᶠ[𝓝 x] OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ G) e := by
      filter_upwards [hc.fderiv (𝕜 := ℝ)] with z hz
      exact congrArg (fun T => T e) hz
    have hr₁ := hR₁ x hx
    simp only [fieldCommutator, hw.fderiv_eq (𝕜 := ℝ), (hw.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)] at hr₁
    have hr₂ := hR₂ x hx
    rw [hd.fderiv_eq (𝕜 := ℝ)] at hr₂
    change _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x, subset_closure hx⟩ +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value R₁ ⟨x, subset_closure hx⟩ + OAI.Analysis.Normed.Function.Holder.HolderMap.value R₂ ⟨x, subset_closure hx⟩
    rw [hQ x hx, hr₁, hr₂]
    exact log_equation_chart_tangent hG hP e x hu.contDiffAt (hf x hx) (hinv x hx) (heq x hx)
  · exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hn₁)) hn₂)

end OAI.Analysis.PDE.Elliptic
