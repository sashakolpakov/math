import OAI.Analysis.Normed.Function.Holder.C2HolderLattice
import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity

open Set Module
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.Analysis.PDE.Dirichlet

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] [NormedSpace ℝ F] in
/-- Periodicity of a continuous boundary field follows from periodicity in
the dense interior. No boundary differentiability is required. -/
theorem latticePeriodic_boundary_field
    (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ K))
    {f : E → F} (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) (g : K →ᵇ F)
    (heq : EqOn (boundedZeroExtension g) f Ω) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension g) := by
  intro x l
  let t : E := e.symm ((l : P), 0)
  have hKmap : MapsTo (fun y : E ↦ t + y) K K := by
    intro y hy
    have h := hKper y l
    rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] at h
    exact h.mpr hy
  have hΩmap : MapsTo (fun y : E ↦ t + y) Ω Ω := by
    intro y hy
    have h := hΩper y l
    rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] at h
    exact h.mpr hy
  have hi : EqOn (fun y : E ↦ boundedZeroExtension g (t + y))
      (boundedZeroExtension g) Ω := by
    intro y hy
    calc
      boundedZeroExtension g (t + y) = f (t + y) := heq (hΩmap hy)
      _ = f y := by simpa only [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] using hf y l
      _ = boundedZeroExtension g y := (heq hy).symm
  have hc : ContinuousOn (fun y : E ↦ boundedZeroExtension g (t + y)) K :=
    (continuousOn_boundedZeroExtension g).comp
      (continuous_const.add continuous_id).continuousOn hKmap
  have hk := hi.of_subset_closure hc (continuousOn_boundedZeroExtension g) hΩK hKΩ
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq]
  by_cases hx : x ∈ K
  · exact hk hx
  · have htx : t + x ∉ K := by
      have h := hKper x l
      rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] at h
      exact fun ht ↦ hx (h.mp ht)
    change boundedZeroExtension g (t + x) = boundedZeroExtension g x
    simp [boundedZeroExtension, OAI.Analysis.PDE.Dirichlet.zeroExtend, hx, htx]

namespace C2Holder

local instance periodicFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance periodicFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance periodicSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance periodicSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

omit [Fintype ι] in
theorem latticePeriodic_secondDerivative (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ K))
    (u : C2Holder (F := F) hΩK α)
    (hu : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (C2Holder.value u))) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b
      (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative u)) := by
  apply latticePeriodic_boundary_field hΩK hKΩ hΩper hKper hu.fderiv.fderiv
  intro x hx
  rw [boundedZeroExtension_apply _ (hΩK hx)]
  exact (C2Holder.genuine_derivatives hΩ u hx).2.symm

end C2Holder
end OAI.Analysis.Normed.Function.Holder
