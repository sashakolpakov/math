import OAI.Analysis.PDE.Weak.Boundary.SmoothChart
import OAI.Analysis.PDE.Weak.Boundary.Chart.Regularity
import OAI.Analysis.PDE.Weak.Boundary.Chart.AE

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Actual smooth-coefficient Dirichlet regularity at a regular curved
boundary. It starts with the H¹ graph closure and a weak equation; no
boundary chart, trace, or higher weak derivative is an input. -/
theorem curved_boundary_weak_solution_classical
    (r : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hr : ContDiff ℝ ∞ r)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    {W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hW : IsOpen W)
    (hell : ∀ z ∈ W, ∀ v, lam * ‖v‖^2 ≤ inner ℝ (A z v) v)
    (p : H1Pair m) (hp : p ∈ H1Zero {z | r z < 0})
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (he : WeakDivergenceEquation (W ∩ {z | r z < 0}) (fun z => A z (p.2 z)) g)
    (q : ℕ) (hq : 2 ≤ q) {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hx : x ∈ W) (hrx : r x = 0) (hreg : fderiv ℝ r x ≠ 0) :
    ∃ (O : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen O ∧ x ∈ O ∧ O ⊆ W ∧ ContDiff ℝ q u ∧
      (∀ᵐ z ∂volume, z ∈ {z | r z < 0} ∩ O → p.1 z = u z) ∧
      (∀ z ∈ O, r z = 0 → u z = 0) := by
  obtain ⟨k, U, V, G, P, hU, hV, hUb, hVb, h0U, hxV, hG, hP, hG0, hPx,
    hGU, hPV, hPG, hGP, hlevel⟩ := exists_smooth_boundary_chart r hr x hreg
  let U₀ := U ∩ G ⁻¹' W
  let V₀ := V ∩ W
  have hU₀ : IsOpen U₀ := hU.inter (hW.preimage hG.continuous)
  have hV₀ : IsOpen V₀ := hV.inter hW
  have hxV₀ : x ∈ V₀ := ⟨hxV, hx⟩
  have h0U₀ : (0 : OAI.Analysis.PDE.Variational.CellCoordinates m) ∈ U₀ := ⟨h0U, by simpa only [mem_preimage, hG0] using hx⟩
  have hG₀ : MapsTo G U₀ V₀ := fun _ hy => ⟨hGU hy.1, hy.2⟩
  have hP₀ : MapsTo P V₀ U₀ := by
    intro z hz
    exact ⟨hPV hz.1, by simpa only [mem_preimage, hGP z hz.1] using hz.2⟩
  have hflat : ∀ y ∈ U₀, G y ∈ {z | r z < 0} ↔ 0 < y k := by
    intro y hy
    have hh := hlevel y hy.1
    rw [hrx, sub_zero] at hh
    change r (G y) < 0 ↔ _
    rw [hh]
    exact neg_neg_iff_pos
  obtain ⟨η, W₀, hW₀, hxW₀, hW₀V₀, hη, hηs, hηsub, hηrange, hηone⟩ :=
    exists_cutoff_with_open_plateau hV₀ hxV₀
  have hηM : ∀ z, |η z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (hηrange z).1]
    exact (hηrange z).2
  obtain ⟨K, hK⟩ := (hasCompactSupport_cellGradient hηs).exists_bound_of_continuous
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp)))
  let p' := cutoffH1Pair η (hη.of_le (by simp)) hηM hK p
  have hp' : p' ∈ H1Zero (V₀ ∩ {z | r z < 0}) :=
    OAI.Analysis.PDE.Weak.H1Zero.cutoff hp η hη hηM hK (fun z hz => ⟨hηsub hz.1, hz.2⟩)
  have hp'eq := OAI.Analysis.PDE.Variational.cutoffH1Pair_eq_on W₀ hW₀ η (hη.of_le (by simp)) hηM hK hηone p
  have hΩ : IsOpen {z | r z < 0} := isOpen_lt hr.continuous continuous_const
  have he' : WeakDivergenceEquation (W₀ ∩ {z | r z < 0}) (fun z => A z (p'.2 z)) g := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on he (fun z hz => ⟨(hW₀V₀ hz.1).2, hz.2⟩)
    · filter_upwards [hp'eq] with z hz
      intro hzW
      rw [(hz hzW.1).2]
    · exact Eventually.of_forall (fun _ _ => rfl)
  obtain ⟨O₀, u₀, hO₀, h0O₀, hO₀U₀, hu₀, heq₀, hzero₀⟩ :=
    chart_weak_solution_classical k hU₀ hV₀ hΩ hW₀
      (hUb.subset inter_subset_left) (hVb.subset inter_subset_left) hG hP hG₀ hP₀
      (fun y hy => hPG y hy.1) (fun z hz => hGP z hz.1) hflat A hA hlam
      (fun z hz => hell z hz.2) p' hp' g hg he' q hq h0U₀ (by rwa [hG0])
  let O := (V₀ ∩ P ⁻¹' O₀) ∩ W₀
  let u := u₀ ∘ P
  have hO : IsOpen O := (hV₀.inter (hO₀.preimage hP.continuous)).inter hW₀
  have hxO : x ∈ O := ⟨⟨hxV₀, by simpa only [mem_preimage, hPx] using h0O₀⟩, hxW₀⟩
  have hback := chart_quasiMeasurePreserving volume hV₀ hU₀ (hUb.subset inter_subset_left)
    hP.continuous (hG.of_le (by simp)) hP₀ hG₀ (fun z hz => hGP z hz.1) (fun y hy => hPG y hy.1)
  have heqback := (ae_restrict_iff' hV₀.measurableSet).mp (hback.ae heq₀)
  refine ⟨O, u, hO, hxO, fun z hz => hz.1.1.2, hu₀.comp (hP.of_le (by simp)), ?_, ?_⟩
  · filter_upwards [heqback, hp'eq] with z hz hz'
    intro hzO
    have hzV₀ : z ∈ V₀ := hzO.2.1.1
    have hpz : P z ∈ U₀ := hP₀ hzV₀
    have hpzk : 0 < (P z) k := (hflat (P z) hpz).mp (by simpa only [hGP z hzV₀.1] using hzO.1)
    have hh := hz hzV₀ ⟨hpzk, hzO.2.1.2⟩
    rw [hGP z hzV₀.1] at hh
    exact (hz' hzO.2.2).1.symm.trans hh
  · intro z hz hrz
    apply hzero₀ (P z) hz.1.2
    have hh := hlevel (P z) (hPV hz.1.1.1)
    rw [hGP z hz.1.1.1, hrx, hrz] at hh
    linarith

end OAI.Analysis.PDE.Weak
