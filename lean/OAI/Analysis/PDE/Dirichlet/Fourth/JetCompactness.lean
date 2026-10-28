import OAI.Analysis.PDE.Dirichlet.Closed.JetCompactness
import OAI.Analysis.PDE.Dirichlet.LocalJetCompactness
import OAI.Analysis.PDE.Dirichlet.LocalSolutionLimit

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
local instance fourthCompactFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCompactFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- One subsequence retains all five actual jet levels on the full closed
regular domain. Only the top level requires a Hölder bound. -/
theorem exists_fourth_jet_locally_uniform_limit_on_closed_domain
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 4 (u k))
    {α C M₀ M₁ M₂ M₃ M₄ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (h₀ : ∀ k x, r x ≤ 0 → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (h₃ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x‖ ≤ M₃)
    (h₄ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x‖ ≤ M₄)
    (hholder : ∀ k x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) y‖ ≤ C*dist x y^α) :
    ∃ (v : {x | r x ≤ 0} → ℝ)
      (G : {x | r x ≤ 0} → E →L[ℝ] ℝ)
      (H : {x | r x ≤ 0} → E →L[ℝ] E →L[ℝ] ℝ)
      (T : {x | r x ≤ 0} → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (Q : {x | r x ≤ 0} → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ Continuous T ∧ Continuous Q ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => u (φ k) x) v atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => fderiv ℝ (u (φ k)) x) G atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => fderiv ℝ (fderiv ℝ (u (φ k))) x) H atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k)))) x) T atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) =>
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k))))) x) Q atTop ∧
        (∀ x, ‖Q x‖ ≤ M₄) ∧ (∀ x y, ‖Q x-Q y‖ ≤ C*dist x y^α) := by
  let D := {x | r x ≤ 0}
  let : LocallyCompactSpace D := (isClosed_le hr.continuous continuous_const).locallyCompactSpace
  have hD₁ (k) : ContDiff ℝ 3 (fderiv ℝ (u k)) := (hu k).fderiv_right (by norm_num)
  have hD₂ (k) : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (u k))) := (hD₁ k).fderiv_right (by norm_num)
  have hD₃ (k) : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) :=
    (hD₂ k).fderiv_right (by norm_num)
  have hD₄ (k) : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))))) :=
    (hD₃ k).fderiv_right (by norm_num)
  have he₀ := equicontinuous_regular_sublevel hr hreg u
    (fun k => (hu k).of_le (by norm_num)) hM₁ h₁
  have he₁ := equicontinuous_regular_sublevel hr hreg (fun k => fderiv ℝ (u k))
    (fun k => (hD₁ k).of_le (by norm_num)) hM₂ h₂
  have he₂ := equicontinuous_regular_sublevel hr hreg (fun k => fderiv ℝ (fderiv ℝ (u k)))
    (fun k => (hD₂ k).of_le (by norm_num)) hM₃ h₃
  have he₃ := equicontinuous_regular_sublevel hr hreg
    (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) hD₃ hM₄ h₄
  have he₄ : Equicontinuous (fun k (x : D) => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x) :=
    equicontinuous_of_uniform_holder
      (u := fun k (x : D) => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x) hα
      (fun k (x : D) (y : D) => hholder k x x.property y y.property)
  obtain ⟨vG, HT, Q, hvG, hHT, hQ, φ, hφ, hvGlim, hHTlim, hQlim⟩ :=
    exists_three_locally_uniform_limits
      (fun k (x : D) => (u k x, fderiv ℝ (u k) x))
      (fun k (x : D) => (fderiv ℝ (fderiv ℝ (u k)) x, fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x))
      (fun k (x : D) => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x)
      (fun k => ((hu k).continuous.comp continuous_subtype_val).prodMk
        ((hD₁ k).continuous.comp continuous_subtype_val))
      (fun k => ((hD₂ k).continuous.comp continuous_subtype_val).prodMk
        ((hD₃ k).continuous.comp continuous_subtype_val))
      (fun k => (hD₄ k).continuous.comp continuous_subtype_val)
      (fun k x => max_le_max (h₀ k x x.property) (h₁ k x x.property))
      (fun k x => max_le_max (h₂ k x x.property) (h₃ k x x.property))
      (fun k x => h₄ k x x.property)
      (equicontinuous_pair he₀ he₁) (equicontinuous_pair he₂ he₃) he₄
  have hQpoint (x : D) : Tendsto
      (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k))))) x) atTop (𝓝 (Q x)) := by
    have h := (locally_uniform_limit_zeroExtend hQlim).tendsto_at x.property
    simpa only [zeroExtend_apply Q x.property] using h
  refine ⟨fun x => (vG x).1, fun x => (vG x).2,
    fun x => (HT x).1, fun x => (HT x).2, Q,
    hvG.fst, hvG.snd, hHT.fst, hHT.snd, hQ, φ, hφ,
    uniformContinuous_fst.comp_tendstoLocallyUniformly hvGlim,
    uniformContinuous_snd.comp_tendstoLocallyUniformly hvGlim,
    uniformContinuous_fst.comp_tendstoLocallyUniformly hHTlim,
    uniformContinuous_snd.comp_tendstoLocallyUniformly hHTlim, hQlim, ?_, ?_⟩
  · intro x
    exact le_of_tendsto ((hQpoint x).norm)
      (Eventually.of_forall (fun k => h₄ (φ k) x x.property))
  · intro x y
    exact le_of_tendsto (((hQpoint x).sub (hQpoint y)).norm)
      (Eventually.of_forall (fun k => hholder (φ k) x x.property y y.property))

end OAI.Analysis.PDE.Dirichlet
