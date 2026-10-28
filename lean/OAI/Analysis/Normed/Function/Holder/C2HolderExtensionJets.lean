import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity
import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetActual

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

local instance extensionJetsFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance extensionJetsFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance extensionJetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance extensionJetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Any genuine C² extension of a stored-jet function has exactly the
stored first and second derivatives, including at boundary points. Only
density of the interior and continuity of the derivative fields are used. -/
theorem derivatives_of_C2_extension
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (u : C2Holder (F := F) hΩK α)
    {g : E → F} (hg : ContDiff ℝ 2 g)
    (he : ∀ x : K, g x = C2Holder.value u x) :
    ∀ x : K, fderiv ℝ g x = C2Holder.firstDerivative u x ∧
      fderiv ℝ (fderiv ℝ g) x = C2Holder.secondDerivative u x := by
  have hlocal (x : E) (hx : x ∈ Ω) :
      g =ᶠ[𝓝 x] boundedZeroExtension (C2Holder.value u) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (he ⟨y,hΩK hy⟩).trans (boundedZeroExtension_apply _ (hΩK hy)).symm
  have hfirst : EqOn (fderiv ℝ g) (boundedZeroExtension (C2Holder.firstDerivative u)) Ω := by
    intro x hx
    exact (hlocal x hx).fderiv_eq.trans (C2Holder.hasFDerivAt_value_extension u hx).fderiv
  have hsecond : EqOn (fderiv ℝ (fderiv ℝ g))
      (boundedZeroExtension (C2Holder.secondDerivative u)) Ω := by
    intro x hx
    have heq : fderiv ℝ g =ᶠ[𝓝 x] boundedZeroExtension (C2Holder.firstDerivative u) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hfirst hy
    exact heq.fderiv_eq.trans (C2Holder.hasFDerivAt_first_extension u hx).fderiv
  have hg₁ : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ g)) := hg₁.fderiv_right (by norm_num)
  have hfirstK := hfirst.of_subset_closure hg₁.continuous.continuousOn
    (continuousOn_boundedZeroExtension (C2Holder.firstDerivative u)) hΩK hKΩ
  have hsecondK := hsecond.of_subset_closure hg₂.continuous.continuousOn
    (continuousOn_boundedZeroExtension (C2Holder.secondDerivative u)) hΩK hKΩ
  intro x
  exact ⟨(hfirstK x.property).trans (boundedZeroExtension_apply _ x.property),
    (hsecondK x.property).trans (boundedZeroExtension_apply _ x.property)⟩

/-- The previous identification applies to every spatial slice of a joint
C² extension. No smoothness of the parameter-to-jet map is assumed here. -/
theorem spatial_derivatives_of_joint_C2_extension
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ} {U : Set Z}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (u : Z → C2Holder (F := F) hΩK α)
    {g : Z × E → F} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ U, ∀ x : K, g (z,x) = C2Holder.value (u z) x) :
    ∀ z ∈ U, ∀ x : K,
      fderiv ℝ (fun y => g (z,y)) x = C2Holder.firstDerivative (u z) x ∧
      fderiv ℝ (fderiv ℝ (fun y => g (z,y))) x = C2Holder.secondDerivative (u z) x := by
  intro z hz
  exact C2Holder.derivatives_of_C2_extension hΩ hKΩ (u z)
    (hg.comp (contDiff_const.prodMk contDiff_id)) (he z hz)

end OAI.Analysis.Normed.Function.Holder.C2Holder
