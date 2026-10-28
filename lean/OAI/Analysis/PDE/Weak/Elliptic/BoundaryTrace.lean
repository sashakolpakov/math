import OAI.Analysis.PDE.Weak.Elliptic.BoundaryTraceEnergy
import OAI.Analysis.PDE.Weak.Elliptic.BoundaryTraceBox

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The genuine zero-boundary graph completion has zero pointwise boundary
values whenever a local continuous representative exists on the positive side.
Only continuity at the boundary point is used. -/
theorem H1Zero.halfspace_boundary_value_zero_within
    (j : Fin (m + 1)) {p : H1Pair m} (hp : p ∈ H1Zero {x | 0 < x j})
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hxU : x₀ ∈ U) (hxj : x₀ j = 0)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContinuousWithinAt u {x | 0 < x j} x₀)
    (heq : ∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ U → p.1 x = u x) :
    u x₀ = 0 := by
  by_contra hne
  let c : ℝ := (u x₀) ^ 2 / 2
  have hc : 0 < c := half_pos (sq_pos_of_ne_zero hne)
  have hclt : c < (u x₀) ^ 2 := by dsimp [c]; nlinarith [sq_pos_of_ne_zero hne]
  have hn : {x : OAI.Analysis.PDE.Variational.CellCoordinates m | c < (u x) ^ 2} ∈ 𝓝[{x | 0 < x j}] x₀ :=
    (hu.pow 2).eventually (Ioi_mem_nhds hclt)
  obtain ⟨O, hO, hOsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hn
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hO (hU.mem_nhds hxU))
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hclosed : ∀ x ∈ Metric.closedBall x₀ r, 0 < x j → x ∈ U ∧ c ≤ (u x) ^ 2 := by
    intro x hx hxpos
    have hxb : x ∈ Metric.ball x₀ ε := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by dsimp [r]; linarith)
    have ht := hball hxb
    exact ⟨ht.2, (hOsub ⟨ht.1, hxpos⟩).le⟩
  let D : ℝ := c * (2 * r) ^ m / 2
  have hD : 0 < D := by dsimp [D]; positivity
  let G : ℝ := ‖p.2‖ ^ 2
  have hG : 0 ≤ G := sq_nonneg _
  let t : ℝ := min r (D / (8 * (G + 1)))
  have ht : 0 < t := lt_min hr (div_pos hD (by positivity))
  have htr : t ≤ r := min_le_left _ _
  have htD : t * (8 * (G + 1)) ≤ D :=
    (le_div_iff₀ (by positivity : 0 < 8 * (G + 1))).mp (min_le_right _ _)
  let a₀ := traceLower x₀ j r 0
  let a₁ := traceLower x₀ j r (t / 2)
  let b := traceUpper x₀ j r t
  have hab : a₀ ≤ b := traceLower_le_traceUpper x₀ j hr.le ht.le
  have hsmall : Icc a₁ b ⊆ Icc a₀ b := traceBox_mono_lower x₀ j (by positivity)
  have hsmallball : Icc a₁ b ⊆ Metric.closedBall x₀ r :=
    traceBox_subset_closedBall x₀ j hxj hr.le (by linarith) htr
  have hsmallpos : Icc a₁ b ⊆ {x | 0 < x j} := traceBox_positive x₀ j (half_pos ht)
  have hpint : Integrable (fun x ↦ (p.1 x) ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p.1)).mp (Lp.memLp p.1)
  have hmass : volume.real (Icc a₁ b) * c ≤ ∫ x in Icc a₁ b, (p.1 x) ^ 2 := by
    calc
      _ = ∫ _x in Icc a₁ b, c := by simp [Measure.real, smul_eq_mul]
      _ ≤ _ := by
        apply integral_mono_ae (continuous_const.integrableOn_Icc) hpint.integrableOn
        filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem measurableSet_Icc] with x hx hxs
        have hl := hclosed x (hsmallball hxs) (hsmallpos hxs)
        rw [hx ⟨hsmallpos hxs, hl.1⟩]
        exact hl.2
  have hmono : (∫ x in Icc a₁ b, (p.1 x) ^ 2) ≤ ∫ x in Icc a₀ b, (p.1 x) ^ 2 :=
    setIntegral_mono_set hpint.integrableOn (ae_of_all _ fun x ↦ sq_nonneg _)
      (ae_of_all _ fun _ hx ↦ hsmall hx)
  have hupper := OAI.Analysis.PDE.Weak.H1Zero.strip_energy j hp a₀ b hab (by simp [a₀, traceLower])
  have hvolume : volume.real (Icc a₁ b) = (t - t / 2) * (2 * r) ^ m :=
    traceBox_volume x₀ j hr.le (by linarith)
  rw [hvolume] at hmass
  have hmain : t * D ≤ 4 * t ^ 2 * G := by
    calc
      _ = ((t - t / 2) * (2 * r) ^ m) * c := by dsimp [D]; ring
      _ ≤ _ := by simpa only [b, traceUpper, Function.update_self, G] using
        hmass.trans (hmono.trans hupper)
  have hcancel : D ≤ 4 * t * G := by nlinarith
  nlinarith

theorem H1Zero.halfspace_boundary_value_zero
    (j : Fin (m + 1)) {p : H1Pair m} (hp : p ∈ H1Zero {x | 0 < x j})
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hxU : x₀ ∈ U) (hxj : x₀ j = 0)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContinuousAt u x₀)
    (heq : ∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ U → p.1 x = u x) :
    u x₀ = 0 :=
  OAI.Analysis.PDE.Weak.H1Zero.halfspace_boundary_value_zero_within j hp hU hxU hxj hu.continuousWithinAt heq

theorem H1Zero.halfspace_boundary_zero_on
    (j : Fin (m + 1)) {p : H1Pair m} (hp : p ∈ H1Zero {x | 0 < x j})
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContinuousOn u U)
    (heq : ∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ U → p.1 x = u x) :
    ∀ x ∈ U, x j = 0 → u x = 0 := by
  intro x hx hxj
  exact OAI.Analysis.PDE.Weak.H1Zero.halfspace_boundary_value_zero j hp hU hx hxj
    (hu.continuousAt (hU.mem_nhds hx)) heq

theorem H1Zero.halfspace_boundary_value_zero_of_subset
    (j : Fin (m + 1)) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hΩ : Ω ⊆ {x | 0 < x j}) {p : H1Pair m} (hp : p ∈ H1Zero Ω)
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hxU : x₀ ∈ U) (hxj : x₀ j = 0)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContinuousAt u x₀)
    (heq : ∀ᵐ x ∂volume, x ∈ {x | 0 < x j} ∩ U → p.1 x = u x) :
    u x₀ = 0 := by
  have hp' : p ∈ H1Zero {x | 0 < x j} := by
    apply closure_mono (s := smoothH1Graph Ω) (t := smoothH1Graph {x | 0 < x j}) _ hp
    rintro q ⟨v, hv, hs, hsub, rfl⟩
    exact ⟨v, hv, hs, hsub.trans hΩ, rfl⟩
  exact OAI.Analysis.PDE.Weak.H1Zero.halfspace_boundary_value_zero j hp' hU hxU hxj hu heq

end OAI.Analysis.PDE.Weak
