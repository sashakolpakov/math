import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Invertibility
import OAI.Analysis.PDE.Dirichlet.PositiveLattice
import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear

noncomputable section
open Set Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

theorem smooth_invertible_image_mem_nhds
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : X → Y} (hF : ContDiff ℝ ∞ F) (u : X) (L : X ≃L[ℝ] Y)
    (hL : fderiv ℝ F u = L.toContinuousLinearMap)
    {O : Set X} (hO : IsOpen O) (hu : u ∈ O) :
    ∀ᶠ f in 𝓝 (F u), ∃ w ∈ O, F w = f ∧ (fderiv ℝ F w).IsInvertible := by
  obtain ⟨G,hG,hGu,hbranch,_⟩ := smooth_localInverse_with_invertible_derivative hF u L hL
  have hGt : Tendsto G (𝓝 (F u)) (𝓝 u) := by
    simpa only [ContinuousAt,hGu] using hG.continuousAt
  filter_upwards [hbranch,hGt.eventually (hO.mem_nhds hu)] with f hf hp
  exact ⟨G f,hp,hf⟩

private theorem continuousAdd_of_normed (X : Type*) [NormedAddCommGroup X] :
    ContinuousAdd X := inferInstance

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance continuityInverseFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance continuityInverseFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance continuityInverseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityInverseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityInverseC2Group {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance continuityInverseC2Space {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance continuityInverseC2Module {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance continuityInverseC2Bounded {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := NormedSpace.toIsBoundedSMul
local instance continuityInverseC2Continuous {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := IsBoundedSMul.continuousSMul
local instance continuityInverseC2Add {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    ContinuousAdd (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := continuousAdd_of_normed _

def PositiveInvertibleMooreNeighborhood
    {Ω D : Set E} {hΩD : Ω ⊆ D} {α : ℝ}
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (hΩ : IsOpen Ω) (hclosure : D ⊆ closure Ω)
    (hΩp : LatticePeriodic e lat (fun x => x ∈ Ω))
    (hDp : LatticePeriodic e lat (fun x => x ∈ D))
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hvp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat) : Prop :=
  let F := periodicMooreDirichletOperator hΩ hclosure hΩp hDp hα OAI.Analysis.Calculus.Quaternion.fourSlots v hvp
  ∀ᶠ f in 𝓝 (F u), ∃ w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat,
    (∀ x : D, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v+w.val)) x)).PosDef) ∧
    F w = f ∧ (fderiv ℝ F w).IsInvertible

/-- One local inverse branch simultaneously preserves positivity and
invertibility of the derivative at its possibly rough solutions. -/
theorem periodicMooreDirichlet_positive_invertible_continuation
    {Ω : Set E} {r : E → ℝ} {hΩD : Ω ⊆ {x | r x ≤ 0}} {α : ℝ}
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V}
    (hΩ : IsOpen Ω) (hclosure : {x | r x ≤ 0} ⊆ closure Ω)
    (hΩp : LatticePeriodic e lat (fun x => x ∈ Ω))
    (hr : Continuous r) (hrp : LatticePeriodic e lat r)
    (hK : IsCompact K) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hvp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat)
    (hpos : ∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v+u.val)) x)).PosDef)
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e lat)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hclosure hΩp
      (hrp.comp (fun t => t ≤ 0)) hα OAI.Analysis.Calculus.Quaternion.fourSlots v hvp) u = L.toContinuousLinearMap) :
    PositiveInvertibleMooreNeighborhood e lat hΩ hclosure hΩp
      (hrp.comp (fun t => t ≤ 0)) hα v hvp u := by
  let : Fact (IsOpen Ω) := ⟨hΩ⟩
  let F := periodicMooreDirichletOperator hΩ hclosure hΩp
    (hrp.comp (fun t => t ≤ 0)) hα OAI.Analysis.Calculus.Quaternion.fourSlots v hvp
  let O : Set (OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat) :=
    {w | ∀ x : latticeSublevelCell e lat K r, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (v+w.val)) ⟨x,x.property.2⟩)).PosDef}
  have hO : IsOpen O := (isOpen_positive_hessian_on_compact
    (hΩK := hΩD) (α := α) hΩ hclosure
    (isCompact_latticeSublevelCell e lat hK hr) inter_subset_right).preimage
      (continuous_const.add continuous_subtype_val)
  have huO : u ∈ O := fun x => hpos ⟨x,x.property.2⟩
  have hF : ContDiff ℝ ∞ F := contDiff_periodicMooreDirichletOperator
    hΩ hclosure hΩp (hrp.comp (fun t => t ≤ 0)) hα OAI.Analysis.Calculus.Quaternion.fourSlots v hvp
  have he := smooth_invertible_image_mem_nhds hF u L hL hO huO
  filter_upwards [he] with f hf
  obtain ⟨w,hp,hf⟩ := hf
  refine ⟨w,?_,hf⟩
  apply (positive_hessian_iff_latticeCell hΩ hclosure hΩp hrp hbounded (v+w.val) ?_).mpr hp
  change LatticePeriodic e lat
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v+OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val))
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_add]
  exact hvp.add w.property.2

end OAI.Analysis.PDE.Dirichlet
