import OAI.Analysis.PDE.Schauder.Calculus.Periodic.ParameterFamily

open Set Filter Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

universe u
variable {Z : Type} {E P V : Type*} {F : Type u} {ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

local instance smoothParameterFunctionGroup : NormedAddCommGroup (Z →L[ℝ] F) := inferInstance
local instance smoothParameterFunctionSpace : NormedSpace ℝ (Z →L[ℝ] F) := inferInstance
local instance smoothParameterHolderGroup {S : Set E} {a : ℝ} :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.HolderMap S F a) := inferInstance
local instance smoothParameterHolderSpace {S : Set E} {a : ℝ} :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap S F a) := inferInstance
local instance smoothParameterTargetGroup {S : Set E} {a : ℝ} :
    NormedAddCommGroup (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap S F a) := inferInstance
local instance smoothParameterTargetSpace {S : Set E} {a : ℝ} :
    NormedSpace ℝ (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap S F a) := inferInstance

theorem contDiffOn_periodic_parameter_family_nat
    (q : ℕ) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set Z} (hU : IsOpen U)
    (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x)) :
    ContDiffOn ℝ q T U := by
  induction q generalizing F with
  | zero =>
      exact contDiffOn_zero.mpr (continuousOn_periodic_parameter_family
        e b hK hr hrp hbounded hα hα1 hU f hf hp T hT)
  | succ q ih =>
      have hfD := contDiffOn_parameterFDerivative hU hf
      have hpD : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => parameterFDerivative f (t,x)) :=
        fun t ht => parameterFDerivative_latticePeriodic e b hU hp ht
      obtain ⟨S,hS⟩ := exists_periodic_parameter_family e b hK hr hrp hbounded hα hα1
        (parameterFDerivative f) hfD hpD
      have hd t (ht : t ∈ U) : HasFDerivAt T (holderTranspose (S t)) t :=
        hasFDerivAt_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU
          f hf hp T S hT hS ht
      have hs := ih (parameterFDerivative f) hfD hpD S hS
      have hg : ContDiffOn ℝ q (fun t => holderTranspose (S t)) U :=
        by
          let L : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Z →L[ℝ] F) α →L[ℝ]
              (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α) := holderTransposeCLM
          have hL : ContDiff ℝ q L := L.contDiff
          simpa only [Function.comp_def] using! hL.comp_contDiffOn hs
      rw [show (↑(q+1) : ℕ∞ω) = (q : ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt,by simp,?_⟩
      exact hg.congr (fun t ht => (hd t ht).fderiv)

/-- Joint spatial smoothness gives genuine Banach-space smoothness in every parameter direction. -/
theorem contDiffOn_periodic_parameter_family
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set Z} (hU : IsOpen U)
    (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x)))
    (T : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hT : ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x)) :
    ContDiffOn ℝ ∞ T U := by
  rw [contDiffOn_infty]
  intro q
  exact contDiffOn_periodic_parameter_family_nat q e b hK hr hrp hbounded hα hα1 hU f hf hp T hT

theorem exists_smooth_periodic_parameter_family
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set Z} (hU : IsOpen U)
    (f : Z × E → F) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hp : ∀ t ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (t,x))) :
    ∃ T : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α, ContDiffOn ℝ ∞ T U ∧
      ∀ t ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x = f (t,x) := by
  obtain ⟨T,hT⟩ := exists_periodic_parameter_family e b hK hr hrp hbounded hα hα1 f hf hp
  exact ⟨T,contDiffOn_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU f hf hp T hT,hT⟩

end OAI.Analysis.PDE.Schauder
