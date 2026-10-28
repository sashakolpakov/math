import OAI.Analysis.PDE.Dirichlet.LocalCompactness
import OAI.Analysis.PDE.Dirichlet.LocalEquicontinuity

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem exists_three_locally_uniform_limits
    {E Y Z W : Type*} [PseudoMetricSpace E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup Y] [ProperSpace Y] [SecondCountableTopology Y] [NormedAddCommGroup Z] [ProperSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup W] [ProperSpace W] [SecondCountableTopology W]
    (f : ℕ → E → Y) (g : ℕ → E → Z) (h : ℕ → E → W)
    (hf : ∀ k, Continuous (f k)) (hg : ∀ k, Continuous (g k)) (hh : ∀ k, Continuous (h k))
    {A B C : ℝ} (hfB : ∀ k x, ‖f k x‖ ≤ A) (hgB : ∀ k x, ‖g k x‖ ≤ B)
    (hhB : ∀ k x, ‖h k x‖ ≤ C)
    (hfe : Equicontinuous f) (hge : Equicontinuous g) (hhe : Equicontinuous h) :
    ∃ (v : E → Y) (G : E → Z) (H : E → W),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun k ↦ f (φ k)) v atTop ∧
      TendstoLocallyUniformly (fun k ↦ g (φ k)) G atTop ∧
      TendstoLocallyUniformly (fun k ↦ h (φ k)) H atTop := by
  let jet : ℕ → E → Y × Z × W := fun k x ↦ (f k x, g k x, h k x)
  have hc (k) : Continuous (jet k) := (hf k).prodMk ((hg k).prodMk (hh k))
  have hb (k x) : ‖jet k x‖ ≤ max A (max B C) :=
    max_le_max (hfB k x) (max_le_max (hgB k x) (hhB k x))
  have he : Equicontinuous jet := equicontinuous_pair hfe (equicontinuous_pair hge hhe)
  obtain ⟨w, hw, φ, hφ, hlim⟩ := exists_locally_uniform_limit_of_equicontinuous jet hc hb he
  refine ⟨fun x ↦ (w x).1, fun x ↦ (w x).2.1, fun x ↦ (w x).2.2,
    hw.fst, hw.snd.fst, hw.snd.snd, φ, hφ, ?_, ?_, ?_⟩
  · exact uniformContinuous_fst.comp_tendstoLocallyUniformly hlim
  · exact (uniformContinuous_fst.comp uniformContinuous_snd).comp_tendstoLocallyUniformly hlim
  · exact (uniformContinuous_snd.comp uniformContinuous_snd).comp_tendstoLocallyUniformly hlim


/-- Simultaneous locally uniform convergence of the full second-order jet
on an open domain, using one subsequence throughout the domain. -/
theorem exists_jet_locally_uniform_limit_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    {M₀ M₁ M₂ : ℝ}
    (h₀ : ∀ k x, x ∈ Ω → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, x ∈ Ω → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, x ∈ Ω → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (hholder : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ α C : ℝ, 0 < α ∧
      ∀ k x, x ∈ K → ∀ y, y ∈ K →
        ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤ C * dist x y ^ α) :
    ∃ (v : Ω → ℝ) (G : Ω → E →L[ℝ] ℝ) (H : Ω → E →L[ℝ] E →L[ℝ] ℝ),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun k (x : Ω) ↦ u (φ k) x) v atTop ∧
      TendstoLocallyUniformly (fun k (x : Ω) ↦ fderiv ℝ (u (φ k)) x) G atTop ∧
      TendstoLocallyUniformly (fun k (x : Ω) ↦ fderiv ℝ (fderiv ℝ (u (φ k))) x) H atTop := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hd₁ (k) : ContDiff ℝ 1 (fderiv ℝ (u k)) := (hu k).fderiv_right (by norm_num)
  have hd₂ (k) : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (u k))) :=
    (hd₁ k).fderiv_right (by norm_num)
  have he₀ : Equicontinuous (fun k (x : Ω) ↦ u k x) :=
    equicontinuous_restrict_of_open_fderiv_bound hΩ
      (fun k x _ ↦ (hu k).differentiable (by norm_num) x) h₁
  have he₁ : Equicontinuous (fun k (x : Ω) ↦ fderiv ℝ (u k) x) :=
    equicontinuous_restrict_of_open_fderiv_bound hΩ
      (fun k x _ ↦ (hd₁ k).differentiable (by norm_num) x) h₂
  have he₂ : Equicontinuous (fun k (x : Ω) ↦ fderiv ℝ (fderiv ℝ (u k)) x) :=
    equicontinuous_restrict_of_compact_holder
      (u := fun k ↦ fderiv ℝ (fderiv ℝ (u k))) hΩ hholder
  exact exists_three_locally_uniform_limits
    (fun k (x : Ω) ↦ u k x) (fun k (x : Ω) ↦ fderiv ℝ (u k) x)
    (fun k (x : Ω) ↦ fderiv ℝ (fderiv ℝ (u k)) x)
    (fun k ↦ (hu k).continuous.comp continuous_subtype_val)
    (fun k ↦ (hd₁ k).continuous.comp continuous_subtype_val)
    (fun k ↦ (hd₂ k).continuous.comp continuous_subtype_val)
    (fun k x ↦ h₀ k x x.property) (fun k x ↦ h₁ k x x.property)
    (fun k x ↦ h₂ k x x.property) he₀ he₁ he₂

end OAI.Analysis.PDE.Dirichlet
