import OAI.Analysis.PDE.Dirichlet.CompactLimit
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.Submodule

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def boundedZeroExtension {K : Set E} (f : K →ᵇ F) : E → F := OAI.Analysis.PDE.Dirichlet.zeroExtend (fun x ↦ f x)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem boundedZeroExtension_apply {K : Set E} (f : K →ᵇ F) {x : E} (hx : x ∈ K) :
    boundedZeroExtension f x = f ⟨x, hx⟩ := OAI.Analysis.PDE.Dirichlet.zeroExtend_apply _ hx

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem boundedZeroExtension_zero {K : Set E} :
    boundedZeroExtension (0 : K →ᵇ F) = 0 := by
  ext x
  by_cases hx : x ∈ K <;> simp [boundedZeroExtension, OAI.Analysis.PDE.Dirichlet.zeroExtend, hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem boundedZeroExtension_add {K : Set E} (f g : K →ᵇ F) :
    boundedZeroExtension (f + g) = boundedZeroExtension f + boundedZeroExtension g := by
  ext x
  by_cases hx : x ∈ K <;> simp [boundedZeroExtension, OAI.Analysis.PDE.Dirichlet.zeroExtend, hx]

omit [NormedSpace ℝ E] in
theorem boundedZeroExtension_smul {K : Set E} (c : ℝ) (f : K →ᵇ F) :
    boundedZeroExtension (c • f) = c • boundedZeroExtension f := by
  ext x
  by_cases hx : x ∈ K <;> simp [boundedZeroExtension, OAI.Analysis.PDE.Dirichlet.zeroExtend, hx]

/-- Compatible value/derivative pairs on a closed domain. The derivative
condition is imposed in its open interior, while both entries are continuous
and bounded on the whole domain. -/
def derivativeGraph {Ω K : Set E} (hΩK : Ω ⊆ K) :
    Submodule ℝ ((K →ᵇ F) × (K →ᵇ (E →L[ℝ] F))) where
  carrier := {p | ∀ x (hx : x ∈ Ω),
    HasFDerivAt (boundedZeroExtension p.1) (p.2 ⟨x, hΩK hx⟩) x}
  zero_mem' := by
    intro x hx
    change HasFDerivAt (boundedZeroExtension (0 : K →ᵇ F)) 0 x
    rw [boundedZeroExtension_zero]
    exact hasFDerivAt_const (0 : F) x
  add_mem' := by
    intro p q hp hq x hx
    change HasFDerivAt (boundedZeroExtension (p.1 + q.1))
      (p.2 ⟨x, hΩK hx⟩ + q.2 ⟨x, hΩK hx⟩) x
    rw [boundedZeroExtension_add]
    exact (hp x hx).add (hq x hx)
  smul_mem' := by
    intro c p hp x hx
    change HasFDerivAt (boundedZeroExtension (c • p.1)) (c • p.2 ⟨x, hΩK hx⟩) x
    rw [boundedZeroExtension_smul]
    exact (hp x hx).const_smul c

theorem isClosed_derivativeGraph {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) :
    IsClosed (derivativeGraph (F := F) hΩK : Set ((K →ᵇ F) × (K →ᵇ (E →L[ℝ] F)))) := by
  let : MetricSpace (K →ᵇ F) := BoundedContinuousFunction.instMetricSpace
  let : MetricSpace (K →ᵇ (E →L[ℝ] F)) := BoundedContinuousFunction.instMetricSpace
  apply IsSeqClosed.isClosed
  intro p q hp hq
  have hf : TendstoUniformly (fun k x ↦ (p k).1 x) q.1 atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_fst.tendsto q).comp hq)
  have hD : TendstoUniformly (fun k x ↦ (p k).2 x) q.2 atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_snd.tendsto q).comp hq)
  have hf' : TendstoUniformly (fun k (x : K) ↦ boundedZeroExtension (p k).1 x)
      (fun x ↦ q.1 x) atTop := by
    have heq : (fun k (x : K) ↦ boundedZeroExtension (p k).1 x) =
        fun k (x : K) ↦ (p k).1 x := by
      funext k x
      exact boundedZeroExtension_apply _ x.property
    rw [heq]
    exact hf
  have hD' : TendstoUniformly (fun k (x : K) ↦ boundedZeroExtension (p k).2 x)
      (fun x ↦ q.2 x) atTop := by
    have heq : (fun k (x : K) ↦ boundedZeroExtension (p k).2 x) =
        fun k (x : K) ↦ (p k).2 x := by
      funext k x
      exact boundedZeroExtension_apply _ x.property
    rw [heq]
    exact hD
  have hflim : TendstoUniformlyOn (fun k ↦ boundedZeroExtension (p k).1)
      (boundedZeroExtension q.1) atTop Ω := (OAI.Analysis.PDE.Dirichlet.uniform_limit_zeroExtend hf').mono hΩK
  have hDlim : TendstoLocallyUniformlyOn (fun k ↦ boundedZeroExtension (p k).2)
      (boundedZeroExtension q.2) atTop Ω :=
    ((OAI.Analysis.PDE.Dirichlet.uniform_limit_zeroExtend hD').mono hΩK).tendstoLocallyUniformlyOn
  intro x hx
  have hh := hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hDlim
    (fun k y hy ↦ by
      rw [boundedZeroExtension_apply _ (hΩK hy)]
      exact hp k y hy)
    (fun y hy ↦ hflim.tendsto_at hy) hx
  rwa [boundedZeroExtension_apply _ (hΩK hx)] at hh

end OAI.Analysis.Normed.Function.Holder
