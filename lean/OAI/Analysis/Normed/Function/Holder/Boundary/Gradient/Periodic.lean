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
local instance gradientPeriodicFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientPeriodicFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

theorem uniform_periodic_gradient_holder_of_local
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
          C*‖U.val‖*dist x y^α) :
    ∃ C > 0, ∀ U : {U : C2Holder (F := ℝ) hΩK α //
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (C2Holder.value U))},
      ∀ x y : {x | r x ≤ 0},
        ‖C2Holder.firstDerivative U.val x-C2Holder.firstDerivative U.val y‖ ≤ C*‖U.val‖*dist x y^α := by
  let Z := {U : C2Holder (F := ℝ) hΩK α //
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (C2Holder.value U))}
  let g : Z → E → (E →L[ℝ] ℝ) := fun U => boundedZeroExtension (C2Holder.firstDerivative U.val)
  have hnorm (U : Z) (x : E) (hx : r x ≤ 0) : ‖g U x‖ ≤ ‖U.val‖ := by
    change ‖boundedZeroExtension (C2Holder.firstDerivative U.val) x‖ ≤ ‖U.val‖
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
    · exact U.property
  let S := cthickening 1 (OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  have hloc : ∀ a ∈ S, ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (U : Z) x, x ∈ S → dist x a ≤ ρ →
        ‖g U x‖ ≤ C*‖U.val‖ ∧ ∀ y, y ∈ S → dist y a ≤ ρ →
          ‖g U x-g U y‖ ≤ C*‖U.val‖*dist x y^α := by
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
    (fun U : Z => ‖U.val‖) (fun U => norm_nonneg U.val) hα hloc
  refine ⟨C+2,by linarith,?_⟩
  intro U x y
  have hhglobal := OAI.Analysis.PDE.Dirichlet.lattice_holder_of_thickened_cell e b hrp hbounded
    (fun _ : Unit => g U) (fun _ => hperiod U) hα.le
    (mul_nonneg hC.le (norm_nonneg U.val)) (norm_nonneg U.val)
    (fun _ => hnorm U) (fun _ x hx y hy => hh U x hx y hy)
  have hb := hhglobal () x x.property y y.property
  change ‖boundedZeroExtension (C2Holder.firstDerivative U.val) x-
    boundedZeroExtension (C2Holder.firstDerivative U.val) y‖ ≤ (C*‖U.val‖+2*‖U.val‖)*dist (x : E) y^α at hb
  rw [boundedZeroExtension_apply _ x.property, boundedZeroExtension_apply _ y.property] at hb
  simpa only [Subtype.dist_eq, add_mul, mul_assoc,
    one_mul] using hb


end OAI.Analysis.Normed.Function.Holder.C2Holder
