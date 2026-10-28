import OAI.Analysis.PDE.Weak.Boundary.L2Pullback
import OAI.Analysis.PDE.Weak.Boundary.GradientPullback
import OAI.Analysis.PDE.Weak.Elliptic.H1
import OAI.Analysis.PDE.Weak.Elliptic.Multiplier

/-! The gradient component of the genuine bounded H¹ chart pullback. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def chartGradientL2 (U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hU : MeasurableSet U)
    (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (hG : ContDiff ℝ 1 G)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M) :
    Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) →L[ℝ]
      Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
  (zeroExtendL2 volume U hU).comp
    ((fieldMultiplierCLM (μ := volume.restrict U) (chartGradientMap G)
      (continuous_chartGradientMap hG).aestronglyMeasurable
      ((ae_restrict_iff' hU).mpr (Eventually.of_forall hM))).comp
      (boundedComposeL2 (volume.restrict U) volume G hG.continuous.measurable hc hmap))

theorem chartGradientL2_ae (U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hU : MeasurableSet U)
    (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (hG : ContDiff ℝ 1 G)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M)
    (u : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) :
    chartGradientL2 U hU G hG hc hmap hM u =ᵐ[volume]
      U.indicator (fun y => chartGradientMap G y (u (G y))) := by
  let w := boundedComposeL2 (volume.restrict U) volume G hG.continuous.measurable hc hmap u
  let hJ := (continuous_chartGradientMap hG).aestronglyMeasurable (μ := volume.restrict U)
  let hB : ∀ᵐ y ∂volume.restrict U, ‖chartGradientMap G y‖ ≤ M :=
    (ae_restrict_iff' hU).mpr (Eventually.of_forall hM)
  let v := fieldMultiplierCLM (chartGradientMap G) hJ hB w
  have hw := (ae_restrict_iff' hU).mp
    (boundedComposeL2_ae (volume.restrict U) volume G hG.continuous.measurable hc hmap u)
  have hv := (ae_restrict_iff' hU).mp (fieldMultiplierCLM_ae (chartGradientMap G) hJ hB w)
  change zeroExtendL2 volume U hU v =ᵐ[volume] _
  filter_upwards [zeroExtendL2_ae volume U hU v, hw, hv] with y hy hw hv
  rw [hy]
  by_cases hh : y ∈ U
  · simp only [indicator_of_mem hh]
    exact (hv hh).trans (congrArg (chartGradientMap G y) (hw hh))
  · simp only [indicator_of_notMem hh]

def chartH1Pair (U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hU : MeasurableSet U)
    (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (hG : ContDiff ℝ 1 G)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M) :
    H1Pair m →L[ℝ] H1Pair m :=
  (chartComposeL2 volume volume U hU G hG.continuous.measurable hc hmap).prodMap
    (chartGradientL2 U hU G hG hc hmap hM)

theorem chartH1Pair_value_ae (U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hU : MeasurableSet U)
    (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (hG : ContDiff ℝ 1 G)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M) (p : H1Pair m) :
    (chartH1Pair U hU G hG hc hmap hM p).1 =ᵐ[volume] U.indicator (fun y => p.1 (G y)) :=
  chartComposeL2_ae volume volume U hU G hG.continuous.measurable hc hmap p.1

theorem chartH1Pair_gradient_ae (U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hU : MeasurableSet U)
    (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (hG : ContDiff ℝ 1 G)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hmap : Measure.map G (volume.restrict U) ≤ c • volume)
    {M : ℝ} (hM : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M) (p : H1Pair m) :
    (chartH1Pair U hU G hG hc hmap hM p).2 =ᵐ[volume]
      U.indicator (fun y => chartGradientMap G y (p.2 (G y))) :=
  chartGradientL2_ae U hU G hG hc hmap hM p.2

end OAI.Analysis.PDE.Weak
