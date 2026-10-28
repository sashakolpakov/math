import OAI.Analysis.Normed.Function.Holder.C2HolderJointClosed
import OAI.Analysis.Calculus.FiniteExtension.NormedSublevelExtension
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension

/-! A genuine global C² function representing a parameterized stored-jet
family near one parameter value, on the entire closed physical domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {Z E F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set Z} {r : E → ℝ} {α : ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}

local instance extensionFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance extensionFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance extensionSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance extensionSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance extensionJetGroup : NormedAddCommGroup (C2Holder (F := F) hΩK α) := inferInstance
local instance extensionJetSpace : NormedSpace ℝ (C2Holder (F := F) hΩK α) := inferInstance

theorem exists_joint_C2_extension_near_parameter
    (hU : IsOpen U) (hr : ContDiff ℝ ∞ r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 2 u U)
    (z₀ : Z) (hz₀ : z₀ ∈ U) :
    ∃ V : Set Z, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ∃ g : Z × E → F, ContDiff ℝ 2 g ∧
        ∀ z ∈ V, ∀ x, r x ≤ 0 → g (z,x) = boundedZeroExtension (C2Holder.value (u z)) x := by
  have huz : ContDiffAt ℝ 2 u z₀ := (hu z₀ hz₀).contDiffAt (hU.mem_nhds hz₀)
  obtain ⟨a,ha,haeq⟩ := OAI.Analysis.PDE.Elliptic.exists_contDiff_extension_near_compact
    (K := {z₀}) isCompact_singleton (fun z hz => by
      have hzz : z = z₀ := mem_singleton_iff.mp hz
      subst z
      exact huz)
  obtain ⟨V,hV,hVopen,hzV⟩ := mem_nhds_iff.mp (haeq z₀ (mem_singleton z₀))
  let R : Z × E → ℝ := fun p => r p.2
  have hR : ContDiff ℝ ∞ R := hr.comp contDiff_snd
  have hRreg : ∀ p, R p = 0 → fderiv ℝ R p ≠ 0 := by
    intro p hp hz
    have hD : fderiv ℝ R p = (fderiv ℝ r p.2).comp (ContinuousLinearMap.snd ℝ Z E) :=
      ((hr.differentiable (by simp) p.2).hasFDerivAt.comp p
        (ContinuousLinearMap.snd ℝ Z E).hasFDerivAt).fderiv
    apply hreg p.2 hp
    ext v
    have hv := congrArg (fun L : Z × E →L[ℝ] ℝ => L (0,v)) hz
    rw [hD] at hv
    change fderiv ℝ r p.2 v = 0 at hv
    exact hv
  have hS : (univ : Set Z) ×ˢ {x | r x ≤ 0} = {p | R p ≤ 0} := by
    ext p
    simp [R]
  have hj : ContDiffOn ℝ 2
      (fun p : Z × E => boundedZeroExtension (C2Holder.value (a p.1)) p.2) {p | R p ≤ 0} := by
    rw [← hS]
    exact C2Holder.contDiffOn_joint_value_closed isOpen_univ (hr.of_le (by simp)) hreg a ha.contDiffOn
  obtain ⟨g,hg,hga⟩ := OAI.Analysis.Calculus.FiniteExtension.exists_contDiff_extension_regular_sublevel_normed
    R hR hRreg (fun p : Z × E => boundedZeroExtension (C2Holder.value (a p.1)) p.2) hj
  refine ⟨V ∩ U,hVopen.inter hU,⟨hzV,hz₀⟩,inter_subset_right,g,hg,?_⟩
  intro z hz x hx
  have he : a z = u z := hV hz.1
  simpa only [he] using hga (z,x) hx

end OAI.Analysis.Normed.Function.Holder.C2Holder
