import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear
import OAI.Analysis.PDE.Dirichlet.Boundary.OperatorLower

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance inverseOperatorFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseOperatorFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseOperatorSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseOperatorSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseOperatorC2Group {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseOperatorC2Space {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseOperatorC2Module {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    Module ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance inverseOperatorC2Bounded {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    IsBoundedSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := NormedSpace.toIsBoundedSMul
local instance inverseOperatorC2Continuous {Ω D : Set E} (hΩD : Ω ⊆ D) (α : ℝ) :
    ContinuousSMul ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := IsBoundedSMul.continuousSMul

def restrictedMooreDerivative
    {Ω D : Set E} (hΩD : Ω ⊆ D) {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap D ℝ α :=
  (fderiv ℝ (mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) g).comp
    (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩD) (α := α) e lat).subtypeL

omit [Fintype ι] in
theorem continuous_restrictedMooreDerivative
    {Ω D : Set E} (hΩD : Ω ⊆ D) {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) :
    Continuous (restrictedMooreDerivative hΩD hα e lat) := by
  have hd := (contDiff_mooreDirichletOperator (hΩK := hΩD) hα OAI.Analysis.Calculus.Quaternion.fourSlots 2).continuous_fderiv
    (by norm_num : (2 : ℕ∞ω) ≠ 0)
  exact hd.clm_comp continuous_const

def HasRestrictedMooreLowerBound
    {Ω D : Set E} (hΩD : Ω ⊆ D) {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) : Prop :=
  ∃ C > 0, ∀ u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat,
    ‖u‖ ≤ C*‖restrictedMooreDerivative hΩD hα e lat g u‖

omit [Fintype ι] in
theorem restrictedMooreDerivative_eq_periodic
    {Ω D : Set E} {hΩD : Ω ⊆ D} {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (hΩ : IsOpen Ω) (hclosure : D ⊆ closure Ω)
    (hΩp : LatticePeriodic e lat (fun x => x ∈ Ω))
    (hDp : LatticePeriodic e lat (fun x => x ∈ D))
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hgp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hclosure hΩp hDp hα OAI.Analysis.Calculus.Quaternion.fourSlots g hgp) 0 = L)
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat) :
    (L u).val = restrictedMooreDerivative hΩD hα e lat g u := by
  have h := fderiv_periodicMooreDirichletOperator_coe hΩ hclosure hΩp hDp hα OAI.Analysis.Calculus.Quaternion.fourSlots g hgp 0 u
  have hLu := congrArg (fun T : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat => (T u).val) hL
  have hzero : g + (0 : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat).val = g := add_zero g
  exact hLu.symm.trans (h.trans (congrArg
    (fun v => fderiv ℝ (mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) v u.val) hzero))

omit [Fintype ι] in
theorem restrictedMooreDerivative_lower_of_equiv
    {Ω D : Set E} {hΩD : Ω ⊆ D} {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (hΩ : IsOpen Ω) (hclosure : D ⊆ closure Ω)
    (hΩp : LatticePeriodic e lat (fun x => x ∈ Ω))
    (hDp : LatticePeriodic e lat (fun x => x ∈ D))
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hgp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hclosure hΩp hDp hα OAI.Analysis.Calculus.Quaternion.fourSlots g hgp) 0 =
      L.toContinuousLinearMap) : HasRestrictedMooreLowerBound hΩD hα e lat g := by
  apply bounded_below_of_equiv_norm
    (F := OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := D) (α := α) e lat)
    (restrictedMooreDerivative hΩD hα e lat g) L
  intro u
  change ‖(L u).val‖ = _
  exact congrArg norm (restrictedMooreDerivative_eq_periodic hα e lat hΩ hclosure
    hΩp hDp g hgp L.toContinuousLinearMap hL u)

theorem restrictedMooreDerivative_bounded_below
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hgp : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψp : LatticePeriodic e lat ψ)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hfield : ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots g) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) :
    HasRestrictedMooreLowerBound hΩD hα.le e lat g := by
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  let hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  let hΩp := hrp.comp (fun t => t < 0)
  let hDp := hrp.comp (fun t => t ≤ 0)
  have hzero : g + (0 : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat).val = g :=
    add_zero g
  obtain ⟨L,hL⟩ := exists_periodicMooreDirichlet_derivative_equiv_unconditional (hΩD := hΩD)
    hn e lat hK hr hrp hbounded hreg hrpos hclosure hα hα1 ψ hψ hψp hψpos g hgp 0
    (fun x => (congrArg (fun v => OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) hzero).trans (hfield x))
  exact restrictedMooreDerivative_lower_of_equiv hα.le e lat hΩ hclosure hΩp hDp g hgp L hL

end OAI.Analysis.PDE.Dirichlet
