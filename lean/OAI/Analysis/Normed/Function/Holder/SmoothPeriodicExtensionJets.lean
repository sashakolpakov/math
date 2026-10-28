import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity

/-! A classical representative of a closed C²,α value has precisely the
stored first and second derivatives, including at the boundary. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance extensionJetFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance extensionJetFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance extensionJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance extensionJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

theorem classical_extension_derivatives (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (U : C2Holder (F := F) hΩK α) (g : E → F) (hg : ContDiff ℝ 2 g)
    (heq : ∀ x : K, g x = C2Holder.value U x) :
    (∀ x : K, fderiv ℝ g x = C2Holder.firstDerivative U x) ∧
      ∀ x : K, fderiv ℝ (fderiv ℝ g) x = C2Holder.secondDerivative U x := by
  have hfirst : EqOn (boundedZeroExtension (C2Holder.firstDerivative U)) (fderiv ℝ g) Ω := by
    intro x hx
    have he : g =ᶠ[𝓝 x] boundedZeroExtension (C2Holder.value U) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [boundedZeroExtension_apply _ (hΩK hy)]
      exact heq ⟨y, hΩK hy⟩
    exact (C2Holder.hasFDerivAt_value_extension U hx).fderiv.symm.trans he.fderiv_eq.symm
  have hg₁ : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ g)) := hg₁.fderiv_right (by norm_num)
  have hfirstK := hfirst.of_subset_closure
    (continuousOn_boundedZeroExtension (C2Holder.firstDerivative U)) hg₁.continuous.continuousOn
    hΩK hKΩ
  have hsecond : EqOn
      (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative U))
      (fderiv ℝ (fderiv ℝ g)) Ω := by
    intro x hx
    have he : boundedZeroExtension (C2Holder.firstDerivative U) =ᶠ[𝓝 x] fderiv ℝ g := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hfirst hy
    exact (C2Holder.hasFDerivAt_first_extension U hx).fderiv.symm.trans he.fderiv_eq
  have hsecondK := hsecond.of_subset_closure
    (continuousOn_boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative U))
    hg₂.continuous.continuousOn hΩK hKΩ
  constructor
  · intro x
    simpa only [boundedZeroExtension_apply _ x.property] using (hfirstK x.property).symm
  · intro x
    simpa only [boundedZeroExtension_apply _ x.property] using (hsecondK x.property).symm

end OAI.Analysis.Normed.Function.Holder.C2Holder
