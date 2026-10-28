import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.CurveTangents

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance interiorRegularityFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance interiorRegularityFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance interiorRegularitySecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorRegularitySecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Interior regularity needs no normal solve: smoothness of every diagonal
second directional derivative gives smoothness of the full Hessian. -/
theorem contDiffAt_four_of_diagonal_hessian
    {f : E → ℝ} {a : E} (hf : ContDiffAt ℝ 2 f a)
    (hd : ∀ v : E, ContDiffAt ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ f) x v v) a) :
    ContDiffAt ℝ 4 f a := by
  have hm (v w : E) : ContDiffAt ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ f) x v w) a := by
    have hc : ContDiffAt ℝ 2 (fun x ↦ (1/2 : ℝ) *
        ((fderiv ℝ (fderiv ℝ f) x (v+w) (v+w) - fderiv ℝ (fderiv ℝ f) x v v) -
          fderiv ℝ (fderiv ℝ f) x w w)) a :=
      contDiffAt_const.mul (((hd (v+w)).sub (hd v)).sub (hd w))
    apply hc.congr_of_eventuallyEq
    filter_upwards [hf.eventually (by norm_num)] with x hx
    have hs := (hx.isSymmSndFDerivAt (by norm_num)).eq v w
    simp only [map_add,add_apply]
    linarith
  have hD : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ f)) a := by
    rw [← contDiffWithinAt_univ]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    apply contDiffWithinAt_clm_apply.mpr
    intro w
    exact (hm v w).contDiffWithinAt
  exact contDiffAt_of_hessian_field (k := 2) hf hD

variable {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
local instance interiorRegularityHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance
local instance interiorRegularityHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) := inferInstance

/-- The smooth geometric solution curves supply interior C⁴ regularity of
the actual C² solution. Their identity is required only as a scalar germ at
each point of a direction-dependent neighborhood. -/
theorem contDiffAt_four_of_interior_parameter_curves
    (hΩ : IsOpen Ω) {a : E} (ha : a ∈ Ω)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hcurves : ∀ v : E, ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      ∃ U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ContDiffAt ℝ 2 U 0 ∧
        ∀ x (hx : x ∈ Ω ∩ O),
          (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨x,hΩK hx.1⟩) =ᶠ[𝓝 0]
            fun t ↦ f (x + t • v)) :
    ContDiffAt ℝ 4 f a := by
  apply contDiffAt_four_of_diagonal_hessian hf.contDiffAt
  intro v
  obtain ⟨O,hO,haO,U,hU,he⟩ := hcurves v
  obtain ⟨W,hW⟩ := exists_second_tangent_jet_of_parameter_curve hU id
    (fun x hx ↦ hΩK hx.1) f v (fun _ _ ↦ hf.contDiffAt) he
  have hd := second_tangent_contDiffOn_of_jet hΩ (hΩ.inter hO)
    (G := id) contDiffOn_id (fun x hx ↦ hx.1) v v W hW
  exact (hd a ⟨ha,haO⟩).contDiffAt ((hΩ.inter hO).mem_nhds ⟨ha,haO⟩)

/-- The geometric curve represents the unknown minus the prescribed
smooth background. Adding that background back retains the C⁴ gain. -/
theorem contDiffAt_four_of_interior_geometric_curves
    (hΩ : IsOpen Ω) {a : E} (ha : a ∈ Ω)
    {ψ B : E → ℝ} (hψ : ContDiff ℝ 2 ψ) (hB : ContDiff ℝ 4 B)
    (hcurves : ∀ v : E, ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      ∃ U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ContDiffAt ℝ 2 U 0 ∧
        ∀ x (hx : x ∈ Ω ∩ O),
          (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨x,hΩK hx.1⟩) =ᶠ[𝓝 0]
            fun t ↦ ψ (x + t • v) - B (x + t • v)) :
    ContDiffAt ℝ 4 ψ a := by
  have hf := contDiffAt_four_of_interior_parameter_curves hΩ ha
    (hψ.sub (hB.of_le (by norm_num))) hcurves
  have hs := hf.add hB.contDiffAt
  simpa only [sub_add_cancel] using hs

end OAI.Analysis.PDE.Dirichlet
