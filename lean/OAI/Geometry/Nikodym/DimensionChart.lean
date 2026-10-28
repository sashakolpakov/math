import OAI.Geometry.Nikodym.Hausdorff
import OAI.Geometry.Nikodym.Chart.Geometry

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set _root_.MeasureTheory
open scoped ENNReal

namespace OAI.Geometry.Nikodym

variable {M : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {n : ℕ} {K L : NNReal} {f : M → Space n} {g : Space n → M}
variable {S E Ω : Set M} {T : Set (Space n)}

omit [MeasurableSpace M] [BorelSpace M] in
/-- A bi-Lipschitz chart preserves the dimension of the part of a set
inside its source, without requiring that set to be measurable. -/
theorem dimH_inter_eq_image
    (hf : LipschitzOnWith K f S) (hg : LipschitzOnWith L g T)
    (hmap : MapsTo f S T) (hinv : ∀ x ∈ S, g (f x) = x) :
    dimH (E ∩ S) = dimH (f '' (E ∩ S)) := by
  have himage : f '' (E ∩ S) ⊆ T := by
    rintro _ ⟨x,hx,rfl⟩
    exact hmap hx.2
  have hsub : E ∩ S ⊆ g '' (f '' (E ∩ S)) := by
    intro x hx
    exact ⟨f x,⟨x,hx,rfl⟩,hinv x hx.2⟩
  exact le_antisymm ((dimH_mono hsub).trans ((hg.mono himage).dimH_image_le))
    (hf.mono inter_subset_right).dimH_image_le

/-- Positive one-dimensional incidences transfer to the Euclidean chart.
The geometric hypothesis only asks that each straightened curve fit in
a unit segment through the image of its marked point. In particular,
the curve need not have constant Euclidean length in the chart. -/
theorem hasNikodymSegments_image
    (_ : LipschitzOnWith K f S) (hg : LipschitzOnWith L g T)
    (hmap : MapsTo f S T) (hinv : ∀ x ∈ S, g (f x) = x)
    (hL : 0 < L) {ell : ℝ}
    (hinc : ∀ x ∈ Ω, ∃ I : Set M, I ⊆ S ∧ x ∈ I ∧
      ENNReal.ofReal ell ≤ Measure.hausdorffMeasure 1 (E ∩ I) ∧
      ∃ v a : Space n, ‖v‖ = 1 ∧ f '' I ⊆ OAI.MeasureTheory.Kakeya.unitSegment v a) :
    OAI.Geometry.Nikodym.HasNikodymSegments (f '' (E ∩ S)) (f '' Ω) (ell / (L : ℝ)) := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨I,hI,hxI,hell,v,a,hv,hseg⟩ := hinc x hx
  refine ⟨v,a,hv,hseg ⟨x,hxI,rfl⟩,?_⟩
  have himage : f '' (E ∩ I) ⊆ T := by
    rintro _ ⟨y,hy,rfl⟩
    exact hmap (hI hy.2)
  have hback : E ∩ I ⊆ g '' (f '' (E ∩ I)) := by
    intro y hy
    exact ⟨f y,⟨y,hy,rfl⟩,hinv y (hI hy.2)⟩
  have hlength : Measure.hausdorffMeasure 1 (E ∩ I) ≤
      (L : ℝ≥0∞) * Measure.hausdorffMeasure 1 (f '' (E ∩ I)) :=
    (measure_mono hback).trans (by
      simpa using (hg.mono himage).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1))
  have hsub : f '' (E ∩ I) ⊆ (f '' (E ∩ S)) ∩ OAI.MeasureTheory.Kakeya.unitSegment v a := by
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨⟨y,⟨hy.1,hI hy.2⟩,rfl⟩,hseg ⟨y,hy.2,rfl⟩⟩
  rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < L from hL)]
  simp only [ENNReal.ofReal_coe_nnreal]
  apply (ENNReal.div_le_iff (by exact_mod_cast hL.ne') ENNReal.coe_ne_top).mpr
  calc
    ENNReal.ofReal ell ≤ Measure.hausdorffMeasure 1 (E ∩ I) := hell
    _ ≤ (L : ℝ≥0∞) * Measure.hausdorffMeasure 1 (f '' (E ∩ I)) := hlength
    _ ≤ (L : ℝ≥0∞) * Measure.hausdorffMeasure 1
        ((f '' (E ∩ S)) ∩ OAI.MeasureTheory.Kakeya.unitSegment v a) :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ = _ := mul_comm _ _

/-- The Nikodym dimension conclusion in any actual bi-Lipschitz
straightening chart. Chart construction and Riemannian volume comparison
are separate inputs; no model-chart existence is asserted here. -/
theorem nikodym_dimension_in_chart
    (hN : OAI.Geometry.Nikodym.NikodymMaximalConjecture) (hn : 2 ≤ n)
    (hf : LipschitzOnWith K f S) (hg : LipschitzOnWith L g T)
    (hmap : MapsTo f S T) (hinv : ∀ x ∈ S, g (f x) = x)
    (hL : 0 < L) (hΩ : MeasurableSet (f '' Ω)) (hΩpos : 0 < volume (f '' Ω))
    {ell : ℝ} (hell : 0 < ell)
    (hinc : ∀ x ∈ Ω, ∃ I : Set M, I ⊆ S ∧ x ∈ I ∧
      ENNReal.ofReal ell ≤ Measure.hausdorffMeasure 1 (E ∩ I) ∧
      ∃ v a : Space n, ‖v‖ = 1 ∧ f '' I ⊆ OAI.MeasureTheory.Kakeya.unitSegment v a) :
    dimH (E ∩ S) = n := by
  rw [dimH_inter_eq_image hf hg hmap hinv]
  exact OAI.Geometry.Nikodym.nikodymMaximal_implies_dimension hN n hn _ _ hΩ hΩpos
    (ell / (L : ℝ)) (div_pos hell (show (0 : ℝ) < L from hL))
    (hasNikodymSegments_image hf hg hmap hinv hL hinc)

end OAI.Geometry.Nikodym
