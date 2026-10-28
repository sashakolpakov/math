import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Base
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Density

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance continuityStepFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance continuityStepFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance continuityStepSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityStepSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityStepC2Group {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance continuityStepC2Space {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance continuityStepC2Module {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

def IsRoughPathPoint
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hrp : LatticePeriodic e lat r) (hα : 0 ≤ α)
    (B : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hBp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B)))
    (F₀ F₁ : E → ℝ) (t : ℝ)
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat) : Prop :=
  (∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
    (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x)).PosDef) ∧
  (∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value
    (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x) = densityPath F₀ F₁ t x) ∧
  (fderiv ℝ (periodicMooreDirichletOperator hΩ hclosure
    (hrp.comp (fun t => t < 0)) (hrp.comp (fun t => t ≤ 0)) hα OAI.Analysis.Calculus.Quaternion.fourSlots B hBp) u).IsInvertible

theorem SmoothPathSolution.rough_continuation
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 1 F₀) (hF₁ : ContDiff ℝ 1 F₁)
    (hrp : LatticePeriodic e lat r) (hB₀p : LatticePeriodic e lat B₀)
    (hF₀p : LatticePeriodic e lat F₀) (hF₁p : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hα : 0 < α) (hα1 : α < 1) (B : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hBp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B)))
    (hB₂ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (s : SmoothPathSolution e lat r B₀ F₀ F₁) :
    ∀ᶠ t in 𝓝 s.t, ∃ u, IsRoughPathPoint e lat hΩ hclosure hrp hα.le B hBp F₀ F₁ t u := by
  obtain ⟨u,hu⟩ := s.exists_banach_base e lat hK hr.continuous hrp hbounded
    (hB₀.of_le (by norm_num)) hα.le hα1.le B hB₂
  have hψ : ContDiff ℝ 3 (fun y => B₀ y+s.u y) := (hB₀.add s.smooth).of_le (by norm_num)
  have hp := s.closed_positive (hr.of_le (by simp)) hreg (hB₀.of_le (by norm_num))
    hF₀.continuous hF₁.continuous hpos₀ hpos₁
  obtain ⟨L,hL⟩ := exists_periodicMooreDirichlet_derivative_equiv_unconditional
    (hΩD := hΩD) hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1
    (fun y => B₀ y+s.u y) hψ (hB₀p.add s.periodic) hp B hBp u hu
  have hpu : ∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x)).PosDef := by
    intro x
    rw [hu x]
    exact hp x x.property
  have he := periodicMooreDirichlet_positive_invertible_continuation
    e lat hΩ hclosure (hrp.comp (fun t => t < 0)) hr.continuous hrp hK hbounded hα.le B hBp u hpu L hL
  obtain ⟨f₀,hf₀⟩ := exists_lattice_holder_field e lat hK hr.continuous hrp hbounded F₀ hF₀ hF₀p hα.le hα1.le
  obtain ⟨f₁,hf₁⟩ := exists_lattice_holder_field e lat hK hr.continuous hrp hbounded F₁ hF₁ hF₁p hα.le hα1.le
  let F := periodicMooreDirichletOperator hΩ hclosure (hrp.comp (fun t => t < 0))
    (hrp.comp (fun t => t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots B hBp
  have hFu : F u = densityPathLattice f₀ f₁ s.t := by
    apply Subtype.ext
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value (mooreDirichletOperator hα.le OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x = _
    rw [mooreDirichletOperator,OAI.Analysis.Normed.Function.Holder.value_mooreDetField,hu x,densityPathLattice_value f₀ f₁ hf₀ hf₁]
    exact s.closed_equation (hr.of_le (by simp)) hreg (hB₀.of_le (by norm_num))
      hF₀.continuous hF₁.continuous x x.property
  have ht : Tendsto (densityPathLattice f₀ f₁) (𝓝 s.t) (𝓝 (F u)) := by
    rw [hFu]
    exact (continuous_densityPathLattice f₀ f₁).tendsto s.t
  filter_upwards [ht.eventually he] with t ht
  obtain ⟨w,hwp,hwF,hwi⟩ := ht
  refine ⟨w,hwp,?_,hwi⟩
  intro x
  have hx := congrArg (fun f => OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x) hwF
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (mooreDirichletOperator hα.le OAI.Analysis.Calculus.Quaternion.fourSlots (B+w.val)) x = _ at hx
  rw [mooreDirichletOperator,OAI.Analysis.Normed.Function.Holder.value_mooreDetField] at hx
  exact hx.trans (densityPathLattice_value f₀ f₁ hf₀ hf₁ t x)

end OAI.Analysis.PDE.Dirichlet
