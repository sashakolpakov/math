import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import Mathlib.Topology.Algebra.Group.Basic

/-! # Centered Flattening Normal Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CenteredFlatteningNormalPair

noncomputable section

/-! # An actual support-flattening chart gives an actual centered immersion normal pair -/

open Set Filter
open scoped _root_.Topology

variable {M N E F : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  (f : M → N) (x : M) (e : OpenPartialHomeomorph N (E × F))
  (hx : f x ∈ e.source) (hzero : (e (f x)).2 = 0)
  (hrange : ∀ y ∈ e.source, y ∈ Set.range f ↔ (e y).2 = 0)

/-- Centering changes only the tangential coordinate, leaving the actual normal projection. -/
def centeredFlatteningChart : OpenPartialHomeomorph N (E × F) :=
  e.trans (Homeomorph.subRight ((e (f x)).1, (0 : F))).toOpenPartialHomeomorph

omit [TopologicalSpace M] in
@[simp] theorem centeredFlatteningChart_source :
    (centeredFlatteningChart f x e).source = e.source := by
  simp [centeredFlatteningChart]

omit [TopologicalSpace M] in
@[simp] theorem centeredFlatteningChart_normal (y : N) :
    (centeredFlatteningChart f x e y).2 = (e y).2 := by
  simp [centeredFlatteningChart]

include hzero in
omit [TopologicalSpace M] in
/-- The original center maps to the origin of the genuine product chart. -/
theorem centeredFlatteningChart_center : centeredFlatteningChart f x e (f x) = (0, 0) := by
  apply Prod.ext <;> simp [centeredFlatteningChart, hzero]

include hx hzero in
omit [TopologicalSpace M] in
/-- A product of positive-radius balls lies inside the actual centered target. -/
theorem exists_centeredFlatteningRadius :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆
      (centeredFlatteningChart f x e).target := by
  have hc : (0, 0) ∈ (centeredFlatteningChart f x e).target := by
    rw [← centeredFlatteningChart_center f x e hzero]
    apply (centeredFlatteningChart f x e).map_source
    simpa only [centeredFlatteningChart_source] using hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((centeredFlatteningChart f x e).open_target.mem_nhds hc)
  exact ⟨r, hr, by simpa only [ball_prod_same] using hball⟩

/-- The pair is constructed from the original chart and its original full-image equation. -/
def centeredFlatteningNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x where
  radius := (exists_centeredFlatteningRadius f x e hx hzero).choose
  radius_pos := (exists_centeredFlatteningRadius f x e hx hzero).choose_spec.1
  ambientChart := centeredFlatteningChart f x e
  product_subset_target := (exists_centeredFlatteningRadius f x e hx hzero).choose_spec.2
  point_mem_source := by simpa only [centeredFlatteningChart_source] using hx
  point_coordinates := centeredFlatteningChart_center f x e hzero
  range_iff := by
    rintro y ⟨z, hz, rfl⟩
    have hy := (centeredFlatteningChart f x e).map_target
      ((exists_centeredFlatteningRadius f x e hx hzero).choose_spec.2 hz)
    rw [centeredFlatteningChart_source] at hy
    simpa only [centeredFlatteningChart_normal] using hrange _ hy

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CenteredFlatteningNormalPair
