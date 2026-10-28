import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice
import OAI.Analysis.PDE.Dirichlet.DensityPath

noncomputable section
open Set Filter Module
open scoped Topology
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

private theorem continuityDensityAdd (X : Type*) [NormedAddCommGroup X] :
    ContinuousAdd X := inferInstance
private theorem continuityDensitySMul (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ContinuousSMul ℝ X := inferInstance

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance densityLatticeAdd {D : Set E} {α : ℝ}
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} :
    ContinuousAdd (OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat) :=
  continuityDensityAdd (OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat)
local instance densityLatticeSMul {D : Set E} {α : ℝ}
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} :
    ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat) :=
  continuityDensitySMul (OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat)

theorem exists_lattice_holder_field
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hfp : LatticePeriodic e lat f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T.val x = f x := by
  obtain ⟨T,hT⟩ := exists_periodic_holder_field e lat hK hr hrp hbounded f hf hfp hα hα1
  refine ⟨⟨T,?_⟩,hT⟩
  intro x l
  let y := e.symm ((e x).1+(l : P),(e x).2)
  have hy : r y = r x := hrp x l
  by_cases hx : r x ≤ 0
  · have hy' : r y ≤ 0 := hy ▸ hx
    change OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value T) y = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value T) x
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)
      (show y ∈ {x | r x ≤ 0} from hy'),OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)
      (show x ∈ {x | r x ≤ 0} from hx),hT,hT]
    exact hfp x l
  · have hy' : ¬ r y ≤ 0 := hy ▸ hx
    change OAI.Analysis.Normed.Function.Holder.boundedZeroExtension _ y = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension _ x
    simp only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension,zeroExtend,Set.mem_ofPred_eq,dite_eq_right hx,dite_eq_right hy']

def densityPathLattice {D : Set E} {α : ℝ}
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    (F₀ F₁ : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat) (t : ℝ) :
    OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat :=
  (1-t) • F₀+t • F₁

omit [ProperSpace E] [Fintype ι] in
theorem continuous_densityPathLattice {D : Set E} {α : ℝ}
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    (F₀ F₁ : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat) :
    Continuous (densityPathLattice F₀ F₁) :=
  ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

omit [ProperSpace E] [Fintype ι] in
theorem densityPathLattice_value {D : Set E} {α : ℝ}
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    (F₀ F₁ : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat)
    {f₀ f₁ : E → ℝ} (h₀ : ∀ x : D, OAI.Analysis.Normed.Function.Holder.HolderMap.value F₀.val x = f₀ x)
    (h₁ : ∀ x : D, OAI.Analysis.Normed.Function.Holder.HolderMap.value F₁.val x = f₁ x) (t : ℝ) (x : D) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (densityPathLattice F₀ F₁ t).val x = densityPath f₀ f₁ t x := by
  change (1-t)*OAI.Analysis.Normed.Function.Holder.HolderMap.value F₀.val x+t*OAI.Analysis.Normed.Function.Holder.HolderMap.value F₁.val x = _
  rw [h₀,h₁]
  rfl

end OAI.Analysis.PDE.Dirichlet
