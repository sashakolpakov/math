import OAI.Analysis.PDE.Weak.Elliptic.BoundaryTrace
import OAI.Analysis.PDE.Weak.Boundary.H1Chart

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff ENNReal
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Zero trace passes through a genuine smooth flattening chart. The Sobolev
pullback is the actual bounded graph pullback; no trace or chain-rule axiom is
used. The representative need only be continuous at the boundary point. -/
theorem H1Zero.boundary_value_zero_of_chart
    (j : Fin (m + 1))
    {U V Ω W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hΩ : Ω ⊆ V)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ x ∈ U, P (G x) = x) (hGP : ∀ x ∈ V, G (P x) = x)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M)
    (hflat : ∀ y ∈ U, G y ∈ Ω ↔ 0 < y j)
    {p : H1Pair m} (hp : p ∈ H1Zero Ω)
    {y₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hyU : y₀ ∈ U) (hyj : y₀ j = 0)
    (hW : IsOpen W) (hyW : G y₀ ∈ W)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContinuousAt u (G y₀))
    (heq : ∀ᵐ x ∂volume, x ∈ Ω ∩ W → p.1 x = u x) :
    u (G y₀) = 0 := by
  let q : H1Pair m := chartH1Pair U hU.measurableSet G (hG.of_le (by simp)) hc hmap hM p
  have hq : q ∈ H1Zero (U ∩ G ⁻¹' Ω) :=
    OAI.Analysis.PDE.Weak.H1Zero.chart_pullback hU hV hUb hΩ hG hP hGU hPV hPG hGP hc hmap hM hp
  have hsub : U ∩ G ⁻¹' Ω ⊆ {y | 0 < y j} := by
    intro y hy
    exact (hflat y hy.1).mp hy.2
  have hquasi : Measure.QuasiMeasurePreserving G (volume.restrict U) volume :=
    ⟨hG.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  have hpull : ∀ᵐ y ∂volume, y ∈ U →
      (G y ∈ Ω ∩ W → p.1 (G y) = u (G y)) :=
    (ae_restrict_iff' hU.measurableSet).mp (hquasi.ae heq)
  have hqeq : ∀ᵐ y ∂volume, y ∈ {y | 0 < y j} ∩ (U ∩ G ⁻¹' W) →
      q.1 y = (u ∘ G) y := by
    filter_upwards [chartH1Pair_value_ae U hU.measurableSet G (hG.of_le (by simp))
      hc hmap hM p, hpull] with y hqy hpy
    intro hy
    change q.1 y = u (G y)
    rw [show q.1 y = U.indicator (fun z ↦ p.1 (G z)) y from hqy,
      indicator_of_mem hy.2.1]
    exact hpy hy.2.1 ⟨(hflat y hy.2.1).mpr hy.1, hy.2.2⟩
  exact OAI.Analysis.PDE.Weak.H1Zero.halfspace_boundary_value_zero_of_subset j hsub hq
    (hU.inter (hW.preimage hG.continuous)) ⟨hyU, hyW⟩ hyj
    (hu.comp hG.continuous.continuousAt) hqeq

end OAI.Analysis.PDE.Weak
