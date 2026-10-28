import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Bounded pullback on actual L² equivalence classes, with zero extension
from a measurable chart domain. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped ENNReal
namespace OAI.Analysis.PDE.Weak

variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def boundedComposeL2 (μ : Measure X) (ν : Measure Y) (G : X → Y)
    (hG : Measurable G) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hbound : Measure.map G μ ≤ c • ν) :
    Lp F 2 ν →L[ℝ] Lp F 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ G ⟨hG, rfl⟩).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hc hbound)

theorem boundedComposeL2_ae (μ : Measure X) (ν : Measure Y) (G : X → Y)
    (hG : Measurable G) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hbound : Measure.map G μ ≤ c • ν) (u : Lp F 2 ν) :
    boundedComposeL2 μ ν G hG hc hbound u =ᵐ[μ] fun x => u (G x) := by
  have hm : MeasurePreserving G μ (Measure.map G μ) := ⟨hG, rfl⟩
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans
    (hm.quasiMeasurePreserving.ae (Lp.coeFn_LpToLpOfMeasureLeSMul hc hbound u))

def zeroExtendL2Fun (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (u : Lp F 2 (μ.restrict U)) : Lp F 2 μ :=
  ((memLp_indicator_iff_restrict hU).mpr (Lp.memLp u)).toLp (U.indicator u)

omit [NormedSpace ℝ F] in
theorem zeroExtendL2Fun_ae (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (u : Lp F 2 (μ.restrict U)) : zeroExtendL2Fun μ U hU u =ᵐ[μ] U.indicator u :=
  MemLp.coeFn_toLp _

omit [NormedSpace ℝ F] in
theorem zeroExtendL2Fun_add (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (u v : Lp F 2 (μ.restrict U)) :
    zeroExtendL2Fun μ U hU (u + v) = zeroExtendL2Fun μ U hU u + zeroExtendL2Fun μ U hU v := by
  apply Lp.ext
  have huv := (ae_restrict_iff' hU).mp (Lp.coeFn_add u v)
  filter_upwards [zeroExtendL2Fun_ae μ U hU (u + v),
    Lp.coeFn_add (zeroExtendL2Fun μ U hU u) (zeroExtendL2Fun μ U hU v),
    zeroExtendL2Fun_ae μ U hU u, zeroExtendL2Fun_ae μ U hU v, huv] with x hx ha hu hv hs
  rw [hx, ha]
  simp only [Pi.add_apply, hu, hv]
  by_cases hh : x ∈ U
  · simpa only [indicator_of_mem hh, Pi.add_apply] using hs hh
  · simp only [indicator_of_notMem hh, add_zero]

theorem zeroExtendL2Fun_smul (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (a : ℝ) (u : Lp F 2 (μ.restrict U)) :
    zeroExtendL2Fun μ U hU (a • u) = a • zeroExtendL2Fun μ U hU u := by
  apply Lp.ext
  have hau := (ae_restrict_iff' hU).mp (Lp.coeFn_smul a u)
  filter_upwards [zeroExtendL2Fun_ae μ U hU (a • u),
    Lp.coeFn_smul a (zeroExtendL2Fun μ U hU u), zeroExtendL2Fun_ae μ U hU u, hau]
    with x hx ha hu hs
  rw [hx, ha]
  simp only [Pi.smul_apply, hu]
  by_cases hh : x ∈ U
  · simpa only [indicator_of_mem hh, Pi.smul_apply] using hs hh
  · simp only [indicator_of_notMem hh, smul_zero]

def zeroExtendL2Linear (μ : Measure X) (U : Set X) (hU : MeasurableSet U) :
    Lp F 2 (μ.restrict U) →ₗ[ℝ] Lp F 2 μ where
  toFun := zeroExtendL2Fun μ U hU
  map_add' := zeroExtendL2Fun_add μ U hU
  map_smul' := zeroExtendL2Fun_smul μ U hU

theorem norm_zeroExtendL2Linear (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (u : Lp F 2 (μ.restrict U)) : ‖zeroExtendL2Linear μ U hU u‖ = ‖u‖ := by
  change ‖((memLp_indicator_iff_restrict hU).mpr (Lp.memLp u)).toLp (U.indicator u)‖ = _
  rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict hU]

def zeroExtendL2 (μ : Measure X) (U : Set X) (hU : MeasurableSet U) :
    Lp F 2 (μ.restrict U) →L[ℝ] Lp F 2 μ :=
  (zeroExtendL2Linear μ U hU).mkContinuous 1 (fun u => by
    rw [norm_zeroExtendL2Linear, one_mul])

theorem zeroExtendL2_ae (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (u : Lp F 2 (μ.restrict U)) : zeroExtendL2 μ U hU u =ᵐ[μ] U.indicator u :=
  zeroExtendL2Fun_ae μ U hU u

def chartComposeL2 (μ : Measure X) (ν : Measure Y) (U : Set X) (hU : MeasurableSet U)
    (G : X → Y) (hG : Measurable G) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hbound : Measure.map G (μ.restrict U) ≤ c • ν) : Lp F 2 ν →L[ℝ] Lp F 2 μ :=
  (zeroExtendL2 μ U hU).comp (boundedComposeL2 (μ.restrict U) ν G hG hc hbound)

theorem chartComposeL2_ae (μ : Measure X) (ν : Measure Y) (U : Set X) (hU : MeasurableSet U)
    (G : X → Y) (hG : Measurable G) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hbound : Measure.map G (μ.restrict U) ≤ c • ν) (u : Lp F 2 ν) :
    chartComposeL2 μ ν U hU G hG hc hbound u =ᵐ[μ] U.indicator (fun x => u (G x)) := by
  have ha := (ae_restrict_iff' hU).mp (boundedComposeL2_ae (μ.restrict U) ν G hG hc hbound u)
  change zeroExtendL2 μ U hU (boundedComposeL2 (μ.restrict U) ν G hG hc hbound u) =ᵐ[μ] _
  filter_upwards [zeroExtendL2_ae μ U hU (boundedComposeL2 (μ.restrict U) ν G hG hc hbound u),
    ha] with x hx hy
  rw [hx]
  by_cases hh : x ∈ U
  · simpa [hh] using hy hh
  · simp [hh]

end OAI.Analysis.PDE.Weak
