import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Drift
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension
import OAI.Analysis.PDE.Elliptic.Boundary.HolderActions
import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentChartDerivatives

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.SmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance fourthSource1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthSource1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthSource2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSource2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSource3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSource3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem double_directional_fderiv {u : E → ℝ} (hu : ContDiff ℝ 3 u)
    (v w x h : E) :
    fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) w) x h =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x h w v := by
  have he : OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) w =
      fun y => fderiv ℝ (fderiv ℝ u) y w v := by
    funext y
    exact OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (hu.of_le (by norm_num)) w v y
  rw [he]
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x :=
    ((hu.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h1 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have h2 := h1.clm_apply (hasFDerivAt_const v x)
  rw [h2.fderiv]
  simp

variable {X : Type*} [MetricSpace X] {α : ℝ}

/-- The chart drift acting on a twice-coordinate derivative uses only
the third jet, not a fourth derivative of the solution. -/
def holderDoubleDirectionalDrift (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (v w : E) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  holderEvaluate (holderEvaluate (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D V) w) v

omit [FiniteDimensional ℝ E] in
theorem holderDoubleDirectionalDrift_norm_le (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖holderDoubleDirectionalDrift hα D V v w‖ ≤ 2*‖D‖*‖V‖ := by
  exact (holderEvaluate_norm_le _ hv).trans
    ((holderEvaluate_norm_le _ hw).trans (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα D V))

/-- Transport an actual second-field equation into a coordinate equation.
The only additional source is the lower-order drift, controlled by D³f. -/
theorem exists_double_chart_source
    (A : E → E →L[ℝ] E) {G P : E → E} (hG : ContDiff ℝ 2 G)
    (hP : ContDiff ℝ 1 P) {q f : E → ℝ} (hq : ContDiff ℝ 2 q)
    (hf : ContDiff ℝ 3 f) {S : Set E} (hα : 0 ≤ α)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hinv : ∀ x ∈ S, (fun y => P (G y)) =ᶠ[𝓝 x] id)
    (heq : ∀ x ∈ S, (q ∘ G) =ᶠ[𝓝 x]
      OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v) w)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap S E α)
    (hF : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = ellipticTrace A q (G x))
    (hD : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x)
    (hV : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = inverseChartDrift A G P x) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α,
      (∀ x : S, ellipticTrace
        (fun y => pullbackEllipticOperator (fderiv ℝ P (G y)) (A (G y)))
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v) w) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) ∧
      ‖R‖ ≤ ‖F‖ + 2*‖D‖*‖V‖ := by
  refine ⟨F + holderDoubleDirectionalDrift hα D V v w, ?_, ?_⟩
  · intro x
    have hg := heq x x.property
    rw [← ellipticTrace_congr_germ _ hg]
    have ht := ellipticTrace_inverse_chart_with_drift A
      (hP.differentiable (by norm_num) (G x)) hG.contDiffAt hq.contDiffAt
      (hinv x x.property)
    change ellipticTrace _ (fun y => q (G y)) x = _
    rw [ht]
    change ellipticTrace A q (G x) + fderiv ℝ (q ∘ G) x
      (inverseChartDrift A G P x) = _
    rw [hg.fderiv_eq, double_directional_fderiv hf]
    change _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + OAI.Analysis.Normed.Function.Holder.HolderMap.value D x (OAI.Analysis.Normed.Function.Holder.HolderMap.value V x) w v
    rw [hF,hD,hV]
  · exact (norm_add_le _ _).trans (add_le_add le_rfl
      (holderDoubleDirectionalDrift_norm_le hα D V hv hw))

/-- Specialization to the actual twice differentiated physical potential.
The chart fields may be normal: tangency is needed for boundary estimates,
but not for this equation or its lower-jet source bound. -/
theorem exists_double_field_chart_source
    (A : E → E →L[ℝ] E) {G P : E → E} (hG : ContDiff ℝ 4 G)
    (hP : ContDiff ℝ 3 P) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    {T W : E → E} (hT : ContDiff ℝ 3 T) (hW : ContDiff ℝ 2 W)
    {S : Set E} (hα : 0 ≤ α) (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hinv : ∀ x ∈ S, (fun y => P (G y)) =ᶠ[𝓝 x] id)
    (hTg : ∀ x ∈ S, T =ᶠ[𝓝 (G x)] chartTangentField G P v)
    (hWg : ∀ x ∈ S, W =ᶠ[𝓝 (G x)] chartTangentField G P w)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap S E α)
    (hF : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x =
      ellipticTrace A (fieldDerivative (fieldDerivative u T) W) (G x))
    (hD : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ G))) x)
    (hV : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = inverseChartDrift A G P x) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α,
      (∀ x : S, ellipticTrace
        (fun y => pullbackEllipticOperator (fderiv ℝ P (G y)) (A (G y)))
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ G) v) w) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) ∧
      ‖R‖ ≤ ‖F‖ + 2*‖D‖*‖V‖ := by
  have hq : ContDiff ℝ 2 (fieldDerivative (fieldDerivative u T) W) :=
    contDiff_fieldDerivative (contDiff_fieldDerivative hu hT (by norm_num)) hW (by norm_num)
  apply exists_double_chart_source A (hG.of_le (by norm_num)) (hP.of_le (by norm_num))
    hq ((hu.comp hG).of_le (by norm_num)) hα v w hv hw hinv ?_ F D V hF hD hV
  intro x hx
  have he := OAI.Analysis.Calculus.SmoothExtension.twice_fieldDerivative_chart_germ (hG.of_le (by norm_num)) hP
    (hu.of_le (by norm_num)) v w x (hinv x hx) (hTg x hx) (hWg x hx)
  filter_upwards [he] with y hy
  change fieldDerivative (fieldDerivative u T) W (G y) = _
  rw [OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice ((hu.comp hG).of_le (by norm_num))]
  exact hy

end OAI.Analysis.PDE.Elliptic
