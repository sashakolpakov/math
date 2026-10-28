import OAI.Geometry.Nikodym.Riemannian.VolumeMap
import OAI.Geometry.Nikodym.Beltrami.SmoothMetric
import OAI.Geometry.Nikodym.Beltrami.Volume

open Set _root_.MeasureTheory Matrix
open scoped RealInnerProductSpace ENNReal ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Geometry.Nikodym

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem metricMatrix_beltramiSmoothMetric (κ : ℝ) (x : E) :
    (beltramiSmoothMetric κ).metricMatrix x = beltramiMatrix κ x := by
  ext i j
  change (beltramiCoefficient κ x (WithLp.toLp 2 (Pi.single j 1))) i = _
  rw [beltramiMatrix_apply]
  simp only [beltramiCoefficient,_root_.smul_apply,
    _root_.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct,star_trivial,single_dotProduct,one_mul,PiLp.smul_apply,PiLp.sub_apply,
    smul_eq_mul,Pi.single_apply]
  split_ifs <;> ring

theorem volumeDensity_beltramiSmoothMetric (κ : ℝ) (x : E) :
    (beltramiSmoothMetric κ).volumeDensity x = beltramiVolumeDensity κ x := by
  rw [OAI.Geometry.Nikodym.SmoothCoordinateMetric.volumeDensity,metricMatrix_beltramiSmoothMetric]
  rfl

theorem coordinateVolume_beltramiSmoothMetric_restrict (κ : ℝ) {S : Set E}
    (hS : MeasurableSet S) (hpos : ∀ x ∈ S,0<beltramiDenominator κ x) :
    (beltramiSmoothMetric κ).coordinateVolume.restrict S =
      (beltramiVolume κ).restrict S := by
  rw [(beltramiSmoothMetric κ).coordinateVolume_restrict hS hpos,
    beltramiVolume,restrict_withDensity hS]
  congr 1
  funext x
  rw [volumeDensity_beltramiSmoothMetric]

/-- The genuine local space-form chart transports the original coordinate
Riemannian measure to the explicit Beltrami volume. -/
theorem map_coordinateVolume_beltrami (g : SmoothCoordinateMetric E) (κ : ℝ)
    {S : Set E} {F : E → E} {J : E → E →L[ℝ] E}
    (hS : MeasurableSet S) (hSD : S ⊆ g.domain)
    (hpos : ∀ x ∈ S,0<beltramiDenominator κ (F x))
    (hder : ∀ x ∈ S,HasFDerivWithinAt F (J x) S x) (hinj : InjOn F S)
    (hpull : ∀ x ∈ S,∀ u v,g.inner x u v=beltramiMetric κ (F x) (J x u) (J x v)) :
    Measure.map F (g.coordinateVolume.restrict S) =
      (beltramiVolume κ).restrict (F '' S) := by
  have hFS := measurable_image_of_fderivWithin hS hder hinj
  rw [← coordinateVolume_beltramiSmoothMetric_restrict κ hFS]
  · apply g.map_coordinateVolume_restrict (beltramiSmoothMetric κ) hS hSD hpos hder hinj
    simpa only [beltramiSmoothMetric_inner] using hpull
  · rintro y ⟨x,hx,rfl⟩
    exact hpos x hx

end OAI.Geometry.Nikodym
