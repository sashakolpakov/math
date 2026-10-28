import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Periodicity
import OAI.Analysis.PDE.Dirichlet.Periodic.LocalHolder

/-! A bounded gradient lift obtained from local stored-jet bounds. The
periodic globalization shifts both points by the same lattice vector. -/

noncomputable section
open Set Metric Module
open scoped BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

open OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local instance gradientGlobalFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientGlobalFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

theorem uniform_lattice_gradient_holder_of_local
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    (hKΩ : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ a, r a ≤ 0 → ∃ ρ > 0, ∃ C > 0,
      ∀ U : C2Holder (F := ℝ) hΩK α,
        ∀ x ∈ closedBall a ρ, r x ≤ 0 → ∀ y ∈ closedBall a ρ, r y ≤ 0 →
        ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
          C*‖U‖*dist x y^α) :
    ∃ C > 0, ∀ U : C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b,
      ∀ x y : {x | r x ≤ 0},
        ‖C2Holder.firstDerivative U.val x-C2Holder.firstDerivative U.val y‖ ≤ C*‖U‖*dist x y^α := by
  let Z := C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
  let g : Z → E → (E →L[ℝ] ℝ) := fun U => boundedZeroExtension (C2Holder.firstDerivative U.val)
  have hnorm (U : Z) (x : E) (hx : r x ≤ 0) : ‖g U x‖ ≤ ‖U‖ := by
    change ‖boundedZeroExtension (C2Holder.firstDerivative U.val) x‖ ≤ ‖U‖
    rw [boundedZeroExtension_apply (C2Holder.firstDerivative U.val) (show x ∈ {x | r x ≤ 0} from hx)]
    exact ((C2Holder.firstDerivative U.val).norm_coe_le_norm ⟨x,hx⟩).trans (C2Holder.norm_firstDerivative_le U.val)
  have hperiod (U : Z) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (g U) := by
    apply C2Holder.latticePeriodic_firstDerivative (isOpen_lt hr continuous_const) hKΩ
    · intro x l
      change (r (e.symm ((e x).1+(l : P),(e x).2)) < 0) = (r x < 0)
      rw [hrp x l]
    · intro x l
      change (r (e.symm ((e x).1+(l : P),(e x).2)) ≤ 0) = (r x ≤ 0)
      rw [hrp x l]
    · exact U.property.2
  let S := cthickening 1 (OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  have hloc : ∀ a ∈ S, ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (U : Z) x, x ∈ S → dist x a ≤ ρ →
        ‖g U x‖ ≤ C*‖U‖ ∧ ∀ y, y ∈ S → dist y a ≤ ρ →
          ‖g U x-g U y‖ ≤ C*‖U‖*dist x y^α := by
    intro a ha
    obtain ⟨ρ,hρ,C,hC,hbound⟩ := hlocal a ha.2
    refine ⟨ρ,max 1 C,hρ,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
    intro U x hx hxa
    constructor
    · exact (hnorm U x hx.2).trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
    · intro y hy hya
      exact (hbound U.val x hxa hx.2 y hya hy.2).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (by positivity))
  obtain ⟨C,hC,_,hh⟩ := OAI.Analysis.PDE.Elliptic.compact_family_fixed_holder_of_local hS g
    (fun U : Z => ‖U‖) (fun U => norm_nonneg U) hα hloc
  refine ⟨C+2,by linarith,?_⟩
  intro U x y
  have hhglobal := OAI.Analysis.PDE.Dirichlet.lattice_holder_of_thickened_cell e b hrp hbounded
    (fun _ : Unit => g U) (fun _ => hperiod U) hα.le
    (mul_nonneg hC.le (norm_nonneg U)) (norm_nonneg U)
    (fun _ => hnorm U) (fun _ x hx y hy => hh U x hx y hy)
  have hb := hhglobal () x x.property y y.property
  change ‖boundedZeroExtension (C2Holder.firstDerivative U.val) x-
    boundedZeroExtension (C2Holder.firstDerivative U.val) y‖ ≤ (C*‖U‖+2*‖U‖)*dist (x : E) y^α at hb
  rw [boundedZeroExtension_apply _ x.property, boundedZeroExtension_apply _ y.property] at hb
  simpa only [Subtype.dist_eq, add_mul, mul_assoc,
    one_mul] using hb

omit [ProperSpace E] [Fintype ι] in
theorem exists_lattice_gradient_holder_clm_of_bound
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {Ω D : Set E} (hΩD : Ω ⊆ D) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 < C)
    (hbound : ∀ U : C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e b,
      ∀ x y : D,
      ‖C2Holder.firstDerivative U.val x-C2Holder.firstDerivative U.val y‖ ≤ C*‖U‖*dist x y^α) :
    ∃ L : C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e b →L[ℝ]
        HolderMap D (E →L[ℝ] ℝ) α,
      ∀ U, OAI.Analysis.Normed.Function.Holder.HolderMap.value (L U) = C2Holder.firstDerivative U.val := by
  let Z := C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e b
  let T (U : Z) : HolderMap D (E →L[ℝ] ℝ) α :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα (C2Holder.firstDerivative U.val) (hbound U)
  have hT (U : Z) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (T U) = C2Holder.firstDerivative U.val := rfl
  let L₀ : Z →ₗ[ℝ] HolderMap D (E →L[ℝ] ℝ) α := {
    toFun := T
    map_add' := by
      intro U W
      apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
      rfl
    map_smul' := by
      intro c U
      apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
      rfl }
  have hn (U : Z) : ‖L₀ U‖ ≤ max 1 C*‖U‖ := by
    have ht := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα (C2Holder.firstDerivative U.val)
      (mul_nonneg hC.le (norm_nonneg U)) (hbound U)
    refine ht.trans (max_le ?_ ?_)
    · exact (C2Holder.norm_firstDerivative_le U.val).trans
        (le_mul_of_one_le_left (norm_nonneg U) (le_max_left _ _))
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg U)
  exact ⟨L₀.mkContinuous (max 1 C) hn,hT⟩

theorem exists_lattice_gradient_holder_clm_of_local
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    (hKΩ : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ a, r a ≤ 0 → ∃ ρ > 0, ∃ C > 0,
      ∀ U : C2Holder (F := ℝ) hΩK α,
        ∀ x ∈ closedBall a ρ, r x ≤ 0 → ∀ y ∈ closedBall a ρ, r y ≤ 0 →
        ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
          C*‖U‖*dist x y^α) :
    ∃ L : C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b →L[ℝ]
        HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α,
      ∀ U, OAI.Analysis.Normed.Function.Holder.HolderMap.value (L U) = C2Holder.firstDerivative U.val := by
  obtain ⟨C,hC,hbound⟩ := C2Holder.uniform_lattice_gradient_holder_of_local e b hK hr
    hrp hbounded hΩK hKΩ hα hlocal
  exact C2Holder.exists_lattice_gradient_holder_clm_of_bound e b hΩK hα.le hC hbound

end OAI.Analysis.Normed.Function.Holder.C2Holder
