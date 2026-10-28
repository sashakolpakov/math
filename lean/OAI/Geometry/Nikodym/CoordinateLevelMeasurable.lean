import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section
open Set Metric _root_.MeasureTheory

namespace OAI.Geometry.Nikodym

/-- The coordinate image of a distance level, localized to an open source
patch, is Borel. No global measurability of the partial chart is used. -/
theorem measurableSet_coordinate_distance_level
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) {U : Set X} (hU : IsOpen U)
    (hUs : U ⊆ e.source) (A : Set X) (δ : ℝ) :
    MeasurableSet (e '' ({z | infDist z A = δ} ∩ U)) := by
  classical
  let q : Y → ℝ := e.target.piecewise (fun y => infDist (e.symm y) A) (fun _ => 0)
  have hc : ContinuousOn (fun y => infDist (e.symm y) A) e.target :=
    (continuous_infDist_pt A).comp_continuousOn e.symm.continuousOn
  have hq : Measurable q :=
    hc.measurable_piecewise continuousOn_const e.open_target.measurableSet
  have hformula : e '' ({z | infDist z A = δ} ∩ U) = (e '' U) ∩ q ⁻¹' {δ} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxU⟩, rfl⟩
      refine ⟨⟨x, hxU, rfl⟩, ?_⟩
      change q (e x) = δ
      have ht := e.map_source (hUs hxU)
      change e.target.piecewise (fun y => infDist (e.symm y) A) (fun _ => 0) (e x) = δ
      rw [piecewise_eq_of_mem _ _ _ ht, e.left_inv (hUs hxU)]
      exact hx
    · rintro ⟨⟨x, hxU, rfl⟩, hx⟩
      refine ⟨x, ⟨?_, hxU⟩, rfl⟩
      have ht := e.map_source (hUs hxU)
      change e.target.piecewise (fun y => infDist (e.symm y) A) (fun _ => 0) (e x) = δ at hx
      rw [piecewise_eq_of_mem _ _ _ ht, e.left_inv (hUs hxU)] at hx
      exact hx
  rw [hformula]
  exact (e.isOpen_image_of_subset_source hU hUs).measurableSet.inter
    (hq (measurableSet_singleton δ))

end OAI.Geometry.Nikodym
