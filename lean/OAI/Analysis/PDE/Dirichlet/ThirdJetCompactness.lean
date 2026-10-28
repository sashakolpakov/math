import OAI.Analysis.PDE.Dirichlet.Closed.JetCompactness
import OAI.Analysis.PDE.Dirichlet.LocalJetCompactness
import OAI.Analysis.PDE.Dirichlet.LocalSolutionLimit

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
local instance thirdCompactFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdCompactFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdCompactSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdCompactSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdCompactThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdCompactThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- One subsequence retains all four levels of the actual third-order
jet on the entire closed regular domain, including its boundary. Only
the highest jet needs a Hölder bound. -/
theorem exists_third_jet_locally_uniform_limit_on_closed_domain
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 3 (u k))
    {α C M₀ M₁ M₂ M₃ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (h₀ : ∀ k x, r x ≤ 0 → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (h₃ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x‖ ≤ M₃)
    (hholder : ∀ k x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) y‖ ≤ C*dist x y^α) :
    ∃ (v : {x | r x ≤ 0} → ℝ)
      (G : {x | r x ≤ 0} → E →L[ℝ] ℝ)
      (H : {x | r x ≤ 0} → E →L[ℝ] E →L[ℝ] ℝ)
      (T : {x | r x ≤ 0} → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ Continuous T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => u (φ k) x) v atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => fderiv ℝ (u (φ k)) x) G atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => fderiv ℝ (fderiv ℝ (u (φ k))) x) H atTop ∧
        TendstoLocallyUniformly (fun k (x : {x | r x ≤ 0}) => fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k)))) x) T atTop ∧
        (∀ x, ‖T x‖ ≤ M₃) ∧ (∀ x y, ‖T x-T y‖ ≤ C*dist x y^α) := by
  let D := {x | r x ≤ 0}
  let : LocallyCompactSpace D := (isClosed_le hr.continuous continuous_const).locallyCompactSpace
  have hD₁ (k) : ContDiff ℝ 2 (fderiv ℝ (u k)) := (hu k).fderiv_right (by norm_num)
  have hD₂ (k) : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (u k))) := (hD₁ k).fderiv_right (by norm_num)
  have hD₃ (k) : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) :=
    (hD₂ k).fderiv_right (by norm_num)
  have he₀ := equicontinuous_regular_sublevel hr hreg u
    (fun k => (hu k).of_le (by norm_num)) hM₁ h₁
  have he₁ := equicontinuous_regular_sublevel hr hreg (fun k => fderiv ℝ (u k))
    (fun k => (hD₁ k).of_le (by norm_num)) hM₂ h₂
  have he₂ := equicontinuous_regular_sublevel hr hreg (fun k => fderiv ℝ (fderiv ℝ (u k)))
    hD₂ hM₃ h₃
  have he₃ : Equicontinuous (fun k (x : D) => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x) :=
    equicontinuous_of_uniform_holder
      (u := fun k (x : D) => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x) hα
      (fun k (x : D) (y : D) => hholder k x x.property y y.property)
  obtain ⟨vG, H, T, hvG, hH, hT, φ, hφ, hvGlim, hHlim, hTlim⟩ :=
    exists_three_locally_uniform_limits
      (fun k (x : D) => (u k x, fderiv ℝ (u k) x))
      (fun k (x : D) => fderiv ℝ (fderiv ℝ (u k)) x)
      (fun k (x : D) => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x)
      (fun k => ((hu k).continuous.comp continuous_subtype_val).prodMk
        ((hD₁ k).continuous.comp continuous_subtype_val))
      (fun k => (hD₂ k).continuous.comp continuous_subtype_val)
      (fun k => (hD₃ k).continuous.comp continuous_subtype_val)
      (fun k x => max_le_max (h₀ k x x.property) (h₁ k x x.property))
      (fun k x => h₂ k x x.property) (fun k x => h₃ k x x.property)
      (equicontinuous_pair he₀ he₁) he₂ he₃
  have hTpoint (x : D) :
      Tendsto (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k)))) x)
        atTop (𝓝 (T x)) := by
    have h := (locally_uniform_limit_zeroExtend hTlim).tendsto_at x.property
    simpa only [zeroExtend_apply T x.property] using h
  refine ⟨fun x => (vG x).1, fun x => (vG x).2, H, T,
    hvG.fst, hvG.snd, hH, hT, φ, hφ,
    uniformContinuous_fst.comp_tendstoLocallyUniformly hvGlim,
    uniformContinuous_snd.comp_tendstoLocallyUniformly hvGlim, hHlim, hTlim, ?_, ?_⟩
  · intro x
    exact le_of_tendsto ((hTpoint x).norm)
      (Eventually.of_forall (fun k => h₃ (φ k) x x.property))
  · intro x y
    exact le_of_tendsto (((hTpoint x).sub (hTpoint y)).norm)
      (Eventually.of_forall (fun k => hholder (φ k) x x.property y y.property))

end OAI.Analysis.PDE.Dirichlet
