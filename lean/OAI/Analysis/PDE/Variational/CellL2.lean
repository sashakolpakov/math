import OAI.Analysis.PDE.Variational.Poincare
import Mathlib.MeasureTheory.Function.L2Space

open Set _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

abbrev CellCoordinates (m : ℕ) := Fin (m + 1) → ℝ
abbrev CellVectors (m : ℕ) := EuclideanSpace ℝ (Fin (m + 1))

def cellGradient (u : CellCoordinates m → ℝ) (x : CellCoordinates m) : CellVectors m :=
  WithLp.toLp 2 (fun i ↦ fderiv ℝ u x (Pi.single i 1))

@[simp] theorem cellGradient_apply (u : CellCoordinates m → ℝ) (x : CellCoordinates m)
    (i : Fin (m + 1)) : cellGradient u x i = fderiv ℝ u x (Pi.single i 1) := rfl

theorem continuous_cellGradient {u : CellCoordinates m → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (cellGradient u) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) ↦ ℝ)).symm.continuous.comp
    (continuous_pi fun i ↦ OAI.Analysis.PDE.Green.continuous_directional hu (Pi.single i 1))

theorem cellGradient_add {u v : CellCoordinates m → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    cellGradient (u + v) = cellGradient u + cellGradient v := by
  funext x
  ext i
  simp only [cellGradient_apply, fderiv_add (hu x) (hv x), add_apply]
  rfl

theorem cellGradient_smul (c : ℝ) {u : CellCoordinates m → ℝ}
    (hu : Differentiable ℝ u) : cellGradient (c • u) = c • cellGradient u := by
  funext x
  ext i
  simp only [cellGradient_apply, fderiv_const_smul (hu x), smul_apply]
  rfl

theorem memLp_continuous_cell {H : Type*} [NormedAddCommGroup H]
    (a b : CellCoordinates m) {f : CellCoordinates m → H} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Icc a b)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

def cellToL2 {H : Type*} [NormedAddCommGroup H]
    (a b : CellCoordinates m) (f : CellCoordinates m → H) (hf : Continuous f) :
    Lp H 2 (volume.restrict (Icc a b)) := (memLp_continuous_cell a b hf).toLp f

theorem cellToL2_congr {H : Type*} [NormedAddCommGroup H]
    (a b : CellCoordinates m) {f g : CellCoordinates m → H}
    (hf : Continuous f) (hg : Continuous g) (h : f = g) :
    cellToL2 a b f hf = cellToL2 a b g hg := by subst g; rfl

theorem cellGradientToL2_add (a b : CellCoordinates m) {u v : CellCoordinates m → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    cellToL2 a b (cellGradient (u+v)) (continuous_cellGradient (hu.add hv)) =
      cellToL2 a b (cellGradient u) (continuous_cellGradient hu) +
      cellToL2 a b (cellGradient v) (continuous_cellGradient hv) := by
  exact (cellToL2_congr a b (continuous_cellGradient (hu.add hv))
    ((continuous_cellGradient hu).add (continuous_cellGradient hv))
    (cellGradient_add (hu.differentiable (by norm_num))
      (hv.differentiable (by norm_num)))).trans rfl

theorem cellGradientToL2_smul (a b : CellCoordinates m) (c : ℝ)
    {u : CellCoordinates m → ℝ} (hu : ContDiff ℝ 1 u) :
    cellToL2 a b (cellGradient (c • u)) (continuous_cellGradient (hu.const_smul c)) =
      c • cellToL2 a b (cellGradient u) (continuous_cellGradient hu) := by
  exact (cellToL2_congr a b (continuous_cellGradient (hu.const_smul c))
    ((continuous_cellGradient hu).const_smul c)
    (cellGradient_smul c (hu.differentiable (by norm_num)))).trans rfl

theorem norm_sq_toLp_eq_integral {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure X} {f : X → H} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem norm_sq_cellToL2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : CellCoordinates m) (f : CellCoordinates m → H) (hf : Continuous f) :
    ‖cellToL2 a b f hf‖ ^ 2 = ∫ x in Icc a b, ‖f x‖ ^ 2 :=
  norm_sq_toLp_eq_integral (memLp_continuous_cell a b hf)

theorem cell_poincare_gradient
    (a b : CellCoordinates m) (hab : a ≤ b) (j : Fin (m + 1))
    {u : CellCoordinates m → ℝ} (hu : ContDiff ℝ 1 u)
    (hzero : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      u (j.insertNth (b j) y) = 0) :
    ‖cellToL2 a b u hu.continuous‖ ≤
      (2 * (b j - a j)) * ‖cellToL2 a b (cellGradient u) (continuous_cellGradient hu)‖ := by
  have hp := cell_poincare_directional a b hab j hu hzero
  have hdir : (∫ x in Icc a b, (fderiv ℝ u x (Pi.single j 1)) ^ 2) ≤
      ∫ x in Icc a b, ‖cellGradient u x‖ ^ 2 := by
    apply setIntegral_mono_on
      ((OAI.Analysis.PDE.Green.continuous_directional hu (Pi.single j 1)).pow 2).integrableOn_Icc
      (((continuous_cellGradient hu).norm).pow 2).integrableOn_Icc measurableSet_Icc
    intro x _
    change (fderiv ℝ u x (Pi.single j 1)) ^ 2 ≤ ‖cellGradient u x‖ ^ 2
    have hn := PiLp.norm_apply_le (cellGradient u x) j
    simpa only [cellGradient_apply, Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hv := norm_sq_cellToL2 a b u hu.continuous
  simp only [Real.norm_eq_abs, sq_abs] at hv
  have hg := norm_sq_cellToL2 a b (cellGradient u) (continuous_cellGradient hu)
  have hc : 0 ≤ 4 * (b j - a j) ^ 2 := by positivity
  have hsq := hp.trans (mul_le_mul_of_nonneg_left hdir hc)
  rw [← hv, ← hg] at hsq
  have hL : 0 ≤ b j - a j := sub_nonneg.mpr (hab j)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [hsq]

end OAI.Analysis.PDE.Variational
