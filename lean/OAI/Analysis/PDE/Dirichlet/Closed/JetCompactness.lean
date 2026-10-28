import OAI.Analysis.PDE.Dirichlet.Closed.Equicontinuity

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem equicontinuous_restrict_subset {E F J : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace F] {S K : Set E} (hKS : K ⊆ S) (f : J → E → F)
    (hf : Equicontinuous (fun j (x : S) ↦ f j x)) :
    Equicontinuous (fun j (x : K) ↦ f j x) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.equicontinuousAt_iff.mp (hf ⟨x, hKS x.property⟩) ε hε
  exact ⟨δ, hδ, fun y hy j ↦ hd ⟨y, hKS y.property⟩ hy j⟩

/-- Simultaneous value, gradient and Hessian compactness on a compact
portion of the closed physical domain. In contrast to interior-ball
compactness this includes the boundary and needs no convexity of K. -/
theorem exists_jet_uniform_limit_on_regular_closed_domain {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {K : Set E} (hK : IsCompact K) (hKr : K ⊆ {x | r x ≤ 0})
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    {α C M₀ M₁ M₂ : ℝ} (hα : 0 < α) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₀ : ∀ k x, r x ≤ 0 → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (hholder : ∀ k x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤ C * (dist x y) ^ α) :
    ∃ (v : K → ℝ) (G : K → E →L[ℝ] ℝ) (H : K → E →L[ℝ] E →L[ℝ] ℝ),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k (x : K) ↦ u (φ k) x) v atTop ∧
      TendstoUniformly (fun k (x : K) ↦ fderiv ℝ (u (φ k)) x) G atTop ∧
      TendstoUniformly (fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u (φ k))) x) H atTop := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hD (k) : ContDiff ℝ 1 (fderiv ℝ (u k)) := (hu k).fderiv_right (by norm_num)
  have hDD (k) : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (u k))) := (hD k).fderiv_right (by norm_num)
  have he₀ := equicontinuous_regular_sublevel hr hreg u
    (fun k ↦ (hu k).of_le (by norm_num)) hM₁ h₁
  have he₁ := equicontinuous_regular_sublevel hr hreg (fun k ↦ fderiv ℝ (u k)) hD hM₂ h₂
  have he₂ : Equicontinuous (fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u k)) x) :=
    equicontinuous_of_uniform_holder
      (u := fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u k)) x) hα
      (fun k (x : K) (y : K) ↦ hholder k x (hKr x.property) y (hKr y.property))
  exact exists_three_uniform_limits
    (fun k (x : K) ↦ u k x) (fun k (x : K) ↦ fderiv ℝ (u k) x)
    (fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u k)) x)
    (fun k ↦ (hu k).continuous.comp continuous_subtype_val)
    (fun k ↦ (hD k).continuous.comp continuous_subtype_val)
    (fun k ↦ (hDD k).continuous.comp continuous_subtype_val)
    (fun k x ↦ h₀ k x (hKr x.property)) (fun k x ↦ h₁ k x (hKr x.property))
    (fun k x ↦ h₂ k x (hKr x.property))
    (equicontinuous_restrict_subset hKr u he₀)
    (equicontinuous_restrict_subset hKr (fun k ↦ fderiv ℝ (u k)) he₁) he₂

end OAI.Analysis.PDE.Dirichlet
