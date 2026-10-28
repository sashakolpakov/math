import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Fields
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice
import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : E → ℝ} {α : ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
  {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}

def physicalPushback (B₀ : E → ℝ) (Ψ : E → E)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) (x : E) : ℝ :=
  B₀ x + OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val) (Ψ x)

omit [ProperSpace E] [Fintype ι] in
theorem contDiffOn_physicalPushback_of_mapsTo {B₀ : E → ℝ} {Ψ : E → E}
    (hr : Continuous r) (hB : ContDiff ℝ 2 B₀) (hΨ : ContDiff ℝ 2 Ψ)
    (hmap : MapsTo Ψ {x | r x < 0} {x | r x < 0})
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    ContDiffOn ℝ 2 (physicalPushback B₀ Ψ v) {x | r x < 0} :=
  hB.contDiffOn.add ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value
    (isOpen_lt hr continuous_const) v.val).comp hΨ.contDiffOn hmap)

omit [ProperSpace E] [Fintype ι] in
theorem continuousOn_physicalPushback_of_mapsTo {B₀ : E → ℝ} {Ψ : E → E}
    (hB : Continuous B₀) (hΨ : Continuous Ψ)
    (hmap : MapsTo Ψ {x | r x ≤ 0} {x | r x ≤ 0})
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    ContinuousOn (physicalPushback B₀ Ψ v) {x | r x ≤ 0} :=
  hB.continuousOn.add ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _).comp hΨ.continuousOn hmap)

omit [ProperSpace E] [Fintype ι] in
theorem physicalPushback_boundary_of_mapsTo {B₀ : E → ℝ} {Ψ : E → E}
    (hmap : MapsTo Ψ {x | r x = 0} {x | r x = 0})
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    {x : E} (hx : r x = 0) : physicalPushback B₀ Ψ v x = B₀ x := by
  have hΨx : r (Ψ x) = 0 := hmap hx
  unfold physicalPushback
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val)
    (show Ψ x ∈ {x | r x ≤ 0} from hΨx.le)]
  have hz := v.property.1 (⟨Ψ x,hΨx.le⟩ : {x | r x ≤ 0})
    (show Ψ x ∉ {x | r x < 0} by simp only [Set.mem_ofPred_eq,hΨx,lt_self_iff_false,not_false_eq_true])
  rw [hz,add_zero]

omit [ProperSpace E] [Fintype ι] in
theorem contDiffOn_physicalPushback {B₀ : E → ℝ} {Ψ : E → E}
    (hr : Continuous r) (hB : ContDiff ℝ 2 B₀) (hΨ : ContDiff ℝ 2 Ψ)
    (hlevel : ∀ x, r (Ψ x) = r x)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    ContDiffOn ℝ 2 (physicalPushback B₀ Ψ v) {x | r x < 0} := by
  exact hB.contDiffOn.add ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value
    (isOpen_lt hr continuous_const) v.val).comp hΨ.contDiffOn
      (fun x hx => by simpa only [Set.mem_ofPred_eq,hlevel x] using hx))

omit [ProperSpace E] [Fintype ι] in
theorem continuousOn_physicalPushback {B₀ : E → ℝ} {Ψ : E → E}
    (hB : Continuous B₀) (hΨ : Continuous Ψ) (hlevel : ∀ x, r (Ψ x) = r x)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    ContinuousOn (physicalPushback B₀ Ψ v) {x | r x ≤ 0} := by
  exact hB.continuousOn.add ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _).comp hΨ.continuousOn
    (fun x hx => by simpa only [Set.mem_ofPred_eq,hlevel x] using hx))

omit [ProperSpace E] [Fintype ι] in
theorem latticePeriodic_physicalPushback {B₀ : E → ℝ} {Ψ : E → E}
    (hB : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b B₀)
    (hΨ : ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Ψ (x+e.symm ((l:P),0)) = Ψ x+e.symm ((l:P),0))
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (physicalPushback B₀ Ψ v) :=
  hB.add (latticePeriodic_comp_equivariant e b v.property.2 Ψ hΨ)

omit [ProperSpace E] [Fintype ι] in
theorem physicalPushback_boundary {B₀ : E → ℝ} {Ψ : E → E}
    (hlevel : ∀ x, r (Ψ x) = r x)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    {x : E} (hx : r x = 0) : physicalPushback B₀ Ψ v x = B₀ x := by
  have hΨx : r (Ψ x) = 0 := (hlevel x).trans hx
  unfold physicalPushback
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val)
    (show Ψ x ∈ {x | r x ≤ 0} from hΨx.le)]
  have hz := v.property.1 (⟨Ψ x,hΨx.le⟩ : {x | r x ≤ 0})
    (show Ψ x ∉ {x | r x < 0} by simp only [Set.mem_ofPred_eq,hΨx,lt_self_iff_false,not_false_eq_true])
  rw [hz,add_zero]

omit [ProperSpace E] [Fintype ι] in
theorem physicalPushback_pullback {B₀ : E → ℝ} {Φ Ψ : E → E}
    (hinv : Function.LeftInverse Ψ Φ)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (x : {x | r x ≤ 0}) :
    physicalPushback B₀ Ψ v (Φ x) - B₀ (Φ x) = OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val x := by
  simp only [physicalPushback,hinv x,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property,add_sub_cancel_left]

end OAI.Analysis.PDE.Schauder
