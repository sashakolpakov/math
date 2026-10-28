import OAI.Analysis.PDE.Dirichlet.HolderCompactness
import OAI.Analysis.PDE.Dirichlet.DerivativeLimit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

open Set Metric Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem equicontinuous_pair {E Y Z ι : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace Y] [PseudoMetricSpace Z] {f : ι → E → Y} {g : ι → E → Z}
    (hf : Equicontinuous f) (hg : Equicontinuous g) :
    Equicontinuous (fun i x ↦ (f i x, g i x)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.equicontinuousAt_iff.mp (hf x₀) ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.equicontinuousAt_iff.mp (hg x₀) ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x hx i
  exact max_lt (h₁ x (hx.trans_le (min_le_left _ _)) i)
    (h₂ x (hx.trans_le (min_le_right _ _)) i)

theorem equicontinuous_restrict_of_fderiv_bound
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {K : Set E} (hconv : Convex ℝ K)
    {u : ℕ → E → Y} {M : ℝ}
    (hu : ∀ k x, x ∈ K → DifferentiableAt ℝ (u k) x)
    (hbound : ∀ k x, x ∈ K → ‖fderiv ℝ (u k) x‖ ≤ M) :
    Equicontinuous (fun k (x : K) ↦ u k x) := by
  apply equicontinuous_of_uniform_holder (α := 1) (C := M) zero_lt_one
  intro k x y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (hu k) (hbound k) hconv y.property x.property
  simpa only [Real.rpow_one, Subtype.dist_eq, dist_eq_norm] using h

theorem exists_three_uniform_limits
    {E Y Z W : Type*} [MetricSpace E] [CompactSpace E]
    [NormedAddCommGroup Y] [ProperSpace Y] [NormedAddCommGroup Z] [ProperSpace Z]
    [NormedAddCommGroup W] [ProperSpace W]
    (f : ℕ → E → Y) (g : ℕ → E → Z) (h : ℕ → E → W)
    (hf : ∀ k, Continuous (f k)) (hg : ∀ k, Continuous (g k)) (hh : ∀ k, Continuous (h k))
    {A B C : ℝ} (hfB : ∀ k x, ‖f k x‖ ≤ A) (hgB : ∀ k x, ‖g k x‖ ≤ B)
    (hhB : ∀ k x, ‖h k x‖ ≤ C)
    (hfe : Equicontinuous f) (hge : Equicontinuous g) (hhe : Equicontinuous h) :
    ∃ (v : E → Y) (G : E → Z) (H : E → W),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k ↦ f (φ k)) v atTop ∧
      TendstoUniformly (fun k ↦ g (φ k)) G atTop ∧
      TendstoUniformly (fun k ↦ h (φ k)) H atTop := by
  let jet : ℕ → E → Y × Z × W := fun k x ↦ (f k x, g k x, h k x)
  have hc (k) : Continuous (jet k) := (hf k).prodMk ((hg k).prodMk (hh k))
  have hb (k x) : ‖jet k x‖ ≤ max A (max B C) :=
    max_le_max (hfB k x) (max_le_max (hgB k x) (hhB k x))
  have he : Equicontinuous jet := equicontinuous_pair hfe (equicontinuous_pair hge hhe)
  obtain ⟨w, hw, φ, hφ, hlim⟩ := exists_uniform_limit_of_equicontinuous jet hc hb he
  refine ⟨fun x ↦ (w x).1, fun x ↦ (w x).2.1, fun x ↦ (w x).2.2,
    hw.fst, hw.snd.fst, hw.snd.snd, φ, hφ, ?_, ?_, ?_⟩
  · exact uniformContinuous_fst.comp_tendstoUniformly hlim
  · exact (uniformContinuous_fst.comp uniformContinuous_snd).comp_tendstoUniformly hlim
  · exact (uniformContinuous_snd.comp uniformContinuous_snd).comp_tendstoUniformly hlim

/-- Simultaneous compactness of the value, gradient and Hessian. The lower
derivatives are equicontinuous by the mean-value theorem; only the Hessian
needs the Hölder estimate supplied by elliptic regularity. -/
theorem exists_jet_uniform_limit_on_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    {α C M₀ M₁ M₂ : ℝ} (hα : 0 < α)
    (h₀ : ∀ k x, x ∈ K → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, x ∈ K → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (hholder : ∀ k x, x ∈ K → ∀ y, y ∈ K →
      ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤ C * (dist x y) ^ α) :
    ∃ (v : K → ℝ) (G : K → E →L[ℝ] ℝ) (H : K → E →L[ℝ] E →L[ℝ] ℝ),
      Continuous v ∧ Continuous G ∧ Continuous H ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k (x : K) ↦ u (φ k) x) v atTop ∧
      TendstoUniformly (fun k (x : K) ↦ fderiv ℝ (u (φ k)) x) G atTop ∧
      TendstoUniformly (fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u (φ k))) x) H atTop := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hd₁ (k) : ContDiff ℝ 1 (fderiv ℝ (u k)) := (hu k).fderiv_right (by norm_num)
  have hd₂ (k) : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (u k))) :=
    (hd₁ k).fderiv_right (by norm_num)
  have he₀ : Equicontinuous (fun k (x : K) ↦ u k x) :=
    equicontinuous_restrict_of_fderiv_bound hconv
      (fun k x _ ↦ (hu k).differentiable (by norm_num) x) h₁
  have he₁ : Equicontinuous (fun k (x : K) ↦ fderiv ℝ (u k) x) :=
    equicontinuous_restrict_of_fderiv_bound hconv
      (fun k x _ ↦ (hd₁ k).differentiable (by norm_num) x) h₂
  have he₂ : Equicontinuous (fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u k)) x) :=
    equicontinuous_of_uniform_holder (u := fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u k)) x) hα
      (fun k (x : K) (y : K) ↦ hholder k x x.property y y.property)
  exact exists_three_uniform_limits
    (fun k (x : K) ↦ u k x) (fun k (x : K) ↦ fderiv ℝ (u k) x)
    (fun k (x : K) ↦ fderiv ℝ (fderiv ℝ (u k)) x)
    (fun k ↦ (hu k).continuous.comp continuous_subtype_val)
    (fun k ↦ (hd₁ k).continuous.comp continuous_subtype_val)
    (fun k ↦ (hd₂ k).continuous.comp continuous_subtype_val)
    (fun k x ↦ h₀ k x x.property) (fun k x ↦ h₁ k x x.property)
    (fun k x ↦ h₂ k x x.property) he₀ he₁ he₂

end OAI.Analysis.PDE.Dirichlet
