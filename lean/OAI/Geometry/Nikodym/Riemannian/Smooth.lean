import OAI.Geometry.Nikodym.Riemannian.Bundle
import OAI.Geometry.Nikodym.OpenTangent

noncomputable section
open Set Bundle Manifold
open scoped ContDiff

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_metricForm (g : SmoothCoordinateMetric E) :
    ContDiffOn ℝ ∞ g.metricForm g.domain :=
  contDiffOn_const.clm_comp g.smooth

omit [FiniteDimensional ℝ E] in
theorem contMDiff_metricForm (g : SmoothCoordinateMetric E) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x : g.openDomain => g.metricForm x) := by
  intro x
  apply contMDiffAt_subtype_iff.mpr
  exact ((g.contDiffOn_metricForm x x.property).contDiffAt
    (g.isOpen_domain.mem_nhds x.property)).contMDiffAt

/-- The coordinate metric is smooth as a bilinear form on the actual
tangent bundle, not only as a matrix-valued coordinate function. -/
theorem contMDiff_metricSection (g : SmoothCoordinateMetric E) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : g.openDomain => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        x (g.toRiemannianMetric.inner x)) := by
  intro x
  rw [contMDiffAt_section]
  convert! g.contMDiff_metricForm x using 1
  funext y
  ext u v
  simp [hom_trivializationAt_apply,ContinuousLinearMap.inCoordinates,
    SmoothCoordinateMetric.toRiemannianMetric,opens_tangent_symmL]
  rfl

/-- The genuine smooth Riemannian metric induced by the coefficient field. -/
def toContMDiffRiemannianMetric (g : SmoothCoordinateMetric E) :
    ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : g.openDomain => TangentSpace 𝓘(ℝ,E) x) where
  inner := g.toRiemannianMetric.inner
  symm := g.toRiemannianMetric.symm
  pos := g.toRiemannianMetric.pos
  isVonNBounded := g.toRiemannianMetric.isVonNBounded
  contMDiff := g.contMDiff_metricSection

theorem isContMDiffRiemannianBundle (g : SmoothCoordinateMetric E) :
    letI := g.toRiemannianBundle
    IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E
      (fun x : g.openDomain => TangentSpace 𝓘(ℝ,E) x) := by
  let := g.toRiemannianBundle
  exact ⟨g.toRiemannianMetric.inner,g.contMDiff_metricSection,fun _ _ _ => rfl⟩

theorem isContinuousRiemannianBundle (g : SmoothCoordinateMetric E) :
    letI := g.toRiemannianBundle
    IsContinuousRiemannianBundle E
      (fun x : g.openDomain => TangentSpace 𝓘(ℝ,E) x) := by
  let := g.toRiemannianBundle
  exact ⟨g.toRiemannianMetric.inner,g.contMDiff_metricSection.continuous,fun _ _ _ => rfl⟩

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
