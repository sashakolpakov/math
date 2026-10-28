import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetBounds
import OAI.Analysis.Normed.Function.Holder.C2HolderUniformConstruct

open Set Module
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance jetFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance jetFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance jetSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance jetSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A global periodic C³ function determines an actual closed-domain
C²,α Banach jet. All bounds are derived, not supplied as assumptions. -/
theorem exists_periodic_C2Holder_jet
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (u : E → ℝ) (hu : ContDiff ℝ 3 u) (hup : LatticePeriodic e b u)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ∃ C : ℝ, 0 < C ∧ ‖v‖ ≤ C ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative v x = fderiv ℝ u x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x = fderiv ℝ (fderiv ℝ u) x) ∧
      LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)) := by
  have hD : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hD₂ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := hD.fderiv_right (by norm_num)
  obtain ⟨M₀,hM₀,hm₀⟩ := exists_lattice_norm_bound e b hK hr hrp hbounded hu.continuous.continuousOn hup
  obtain ⟨M₁,hM₁,hm₁⟩ := exists_lattice_norm_bound e b hK hr hrp hbounded hD.continuous.continuousOn hup.fderiv
  obtain ⟨M₂,hM₂,hm₂,hh⟩ := periodic_smooth_jet_holder_bound e b hK hr hrp hbounded
    (fderiv ℝ (fderiv ℝ u)) hD₂ hup.fderiv.fderiv hα hα1
  let v := OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff (isOpen_lt hr continuous_const) hΩD hα u
    (hu.of_le (by norm_num)) hm₀ hm₁ hm₂ hh
  have hv (x : {x | r x ≤ 0}) : OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x := rfl
  refine ⟨v,M₀+M₁+M₂,by positivity,?_,hv,fun _ ↦ rfl,fun _ ↦ rfl,?_⟩
  · apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα (by positivity)
    · intro x
      exact (hm₀ x x.property).trans (by linarith)
    · intro x
      exact (hm₁ x x.property).trans (by linarith)
    · intro x
      exact (hm₂ x x.property).trans (by linarith)
    · intro x y
      exact (hh x x.property y y.property).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))
  · exact OAI.Analysis.Normed.Function.Holder.latticePeriodic_of_value_eq (hrp.comp (fun t ↦ t ≤ 0)) v u hup hv

/-- Zero values on the actual level-set boundary place this genuine jet
in the closed periodic Dirichlet subspace. -/
theorem exists_periodic_dirichlet_C2Holder_jet
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (u : E → ℝ) (hu : ContDiff ℝ 3 u) (hup : LatticePeriodic e b u)
    (hu0 : ∀ x, r x = 0 → u x = 0)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ∃ C : ℝ, 0 < C ∧ ‖v‖ ≤ C ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v x = u x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative v x = fderiv ℝ u x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x = fderiv ℝ (fderiv ℝ u) x) ∧
      v ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e b := by
  obtain ⟨v,C,hC,hv,hv₀,hv₁,hv₂,hvp⟩ := exists_periodic_C2Holder_jet e b hK hr hrp hbounded
    (hΩD := hΩD) u hu hup hα hα1
  refine ⟨v,C,hC,hv,hv₀,hv₁,hv₂,?_,hvp⟩
  intro x hx
  rw [hv₀]
  exact hu0 x (le_antisymm x.property (not_lt.mp hx))

end OAI.Analysis.PDE.Dirichlet
