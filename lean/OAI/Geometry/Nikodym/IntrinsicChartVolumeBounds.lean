import OAI.Geometry.Nikodym.IntrinsicChartVolume

noncomputable section
open Set _root_.MeasureTheory
open scoped ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {n : ℕ}
variable {g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))} {κ : ℝ}
  {x₀ : EuclideanSpace ℝ (Fin n)}
variable (C : LocalBeltramiChart g κ x₀)

theorem map_intrinsicVolume_restrict_bounds {A : Set (IntrinsicDomain g)}
    (hAm : MeasurableSet A) (hA : A ⊆ C.intrinsicSource)
    (hsmall : ∀ y ∈ C.intrinsicForward '' A, |κ| * ‖y‖^2 ≤ 1/2) :
    ENNReal.ofReal (Real.sqrt ((2/3 : ℝ)^(n+1))) •
        volume.restrict (C.intrinsicForward '' A) ≤
      Measure.map C.intrinsicForward ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict A) ∧
    Measure.map C.intrinsicForward ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict A) ≤
      ENNReal.ofReal (Real.sqrt ((2 : ℝ)^(n+1))) •
        volume.restrict (C.intrinsicForward '' A) := by
  rw [C.map_intrinsicVolume_restrict hAm hA]
  exact beltramiVolume_restrict_bounds (C.measurableSet_intrinsicForward_image hAm hA) hsmall

/-- The two finite constants required by the maximal-estimate transport
are consequences of the metric determinant, rather than new hypotheses. -/
theorem exists_intrinsicVolume_patch_constants
    {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVm : MeasurableSet V) (hV : V ⊆ C.chart.target)
    (hsmall : ∀ y ∈ V, |κ| * ‖y‖^2 ≤ 1/2) :
    ∃ a b : ℝ≥0∞, a ≠ ⊤ ∧ b ≠ ⊤ ∧
      Measure.map C.intrinsicForward ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict
        (C.intrinsicSource ∩ C.intrinsicForward ⁻¹' V)) ≤ b • volume ∧
      volume.restrict V ≤ a •
        Measure.map C.intrinsicForward ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict
          (C.intrinsicSource ∩ C.intrinsicForward ⁻¹' V)) := by
  rw [C.map_intrinsicVolume_patch hVm hV]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ((2/3 : ℝ)^(n+1)))
  let b : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ((2 : ℝ)^(n+1)))
  have ha : 0 < a := ENNReal.ofReal_pos.mpr
    (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨hlo,hup⟩ := beltramiVolume_restrict_bounds hVm hsmall
  refine ⟨a⁻¹,b,ENNReal.inv_ne_top.mpr ha.ne',ENNReal.ofReal_ne_top,?_,?_⟩
  · exact hup.trans (smul_le_smul_left b Measure.restrict_le_self)
  · have h : a⁻¹ • (a • volume.restrict V) ≤
        a⁻¹ • (beltramiVolume κ).restrict V := smul_le_smul_left a⁻¹ hlo
    simpa only [smul_smul,ENNReal.inv_mul_cancel ha.ne' hat,one_smul] using h

/-- Positive Riemannian measure becomes positive Lebesgue measure in the
constructed chart, as needed by the Hausdorff-dimension argument. -/
theorem volume_intrinsicForward_image_pos {A : Set (IntrinsicDomain g)}
    (hAm : MeasurableSet A) (hA : A ⊆ C.intrinsicSource)
    (hsmall : ∀ y ∈ C.intrinsicForward '' A, |κ| * ‖y‖^2 ≤ 1/2)
    (hpos : 0 < OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g A) :
    0 < volume (C.intrinsicForward '' A) := by
  rw [C.intrinsicVolume_eq_beltramiVolume_image hAm hA] at hpos
  have hup := (beltramiVolume_restrict_bounds
    (C.measurableSet_intrinsicForward_image hAm hA) hsmall).2 Set.univ
  simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,
    Measure.smul_apply,smul_eq_mul] at hup
  by_contra h
  have hz : volume (C.intrinsicForward '' A) = 0 := le_antisymm (le_of_not_gt h) bot_le
  rw [hz,mul_zero] at hup
  exact (not_lt_of_ge hup) hpos

end OAI.Geometry.Nikodym.LocalBeltramiChart
