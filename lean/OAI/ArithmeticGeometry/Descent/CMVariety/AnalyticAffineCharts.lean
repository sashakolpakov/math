import OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Analytic Affine Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticAffineCharts.Abelian.RelativeCharts

noncomputable section

/-!
Charts proved analytic by actual regular-function evaluation are smooth
for the established native affine manifold structure, in both directions.
The coordinate model can be the relative fiber model rather than the
preferred finite-coordinate model of the native atlas.
-/

open ChartedSpace Set
open scoped Classical ContDiff _root_.Manifold _root_.Topology

variable {B E : Type} [CommRing B] [Algebra ℂ B] [IsDomain B] [Algebra.Smooth ℂ B]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "NativeModel" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)

theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates.contMDiffOn
    {c : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E}
    (hc : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates c) :
    ContMDiffOn (𝓘(ℂ, NativeModel)) (𝓘(ℂ, E)) ω c c.source := by
  intro x hx
  let d := chartAt NativeModel x
  have hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) :=
    chart_mem_atlas NativeModel x
  have hxD : d x ∈ d.target ∩ d.symm ⁻¹' c.source :=
    ⟨d.map_source (mem_chart_source NativeModel x), by
      change d.symm (d x) ∈ c.source
      rw [d.left_inv (mem_chart_source NativeModel x)]
      exact hx⟩
  have hD : IsOpen (d.target ∩ d.symm ⁻¹' c.source) :=
    d.isOpen_inter_preimage_symm c.open_source
  have h := (hc NativeModel d.symm d.target hd.1).contDiffAt (hD.mem_nhds hxD)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id]
    using h.contMDiffAt.contMDiffWithinAt (s := (univ : Set NativeModel))

theorem inverseRegular_contMDiffOn
    (c : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E)
    (hc : ∀ b : B, ContDiffOn ℂ ω (fun v => c.symm v b) c.target) :
    ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, NativeModel)) ω c.symm c.target := by
  intro v hv
  let d := chartAt NativeModel (c.symm v)
  have hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) :=
    chart_mem_atlas NativeModel (c.symm v)
  have hdreg : RegularRelativeCharts.Abelian.RelativeCharts.HasRegularCoordinates d := hd.2
  have hvD : v ∈ c.target ∩ c.symm ⁻¹' d.source :=
    ⟨hv, mem_chart_source NativeModel (c.symm v)⟩
  have hD : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
    c.isOpen_inter_preimage_symm d.open_source
  have h := (hdreg.contDiffOn c.symm c.target hc).contDiffAt (hD.mem_nhds hvD)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_target.mpr
  refine ⟨c.symm.continuousAt hv, ?_⟩
  simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def, id_eq]
    using h.contMDiffAt

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem _root_.OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates.real_contMDiffOn
    {c : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E}
    (hc : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates c) :
    ContMDiffOn (𝓘(ℝ, NativeModel)) (𝓘(ℝ, E)) ω c c.source := by
  intro x hx
  let d := chartAt NativeModel x
  have hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) :=
    chart_mem_atlas NativeModel x
  have hxD : d x ∈ d.target ∩ d.symm ⁻¹' c.source :=
    ⟨d.map_source (mem_chart_source NativeModel x), by
      change d.symm (d x) ∈ c.source
      rw [d.left_inv (mem_chart_source NativeModel x)]
      exact hx⟩
  have hD : IsOpen (d.target ∩ d.symm ⁻¹' c.source) :=
    d.isOpen_inter_preimage_symm c.open_source
  have h := ((hc NativeModel d.symm d.target hd.1).restrict_scalars ℝ).contDiffAt
    (hD.mem_nhds hxD)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id]
    using h.contMDiffAt.contMDiffWithinAt (s := (univ : Set NativeModel))

theorem inverseRegular_real_contMDiffOn
    (c : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E)
    (hc : ∀ b : B, ContDiffOn ℂ ω (fun v => c.symm v b) c.target) :
    ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, NativeModel)) ω c.symm c.target := by
  intro v hv
  let d := chartAt NativeModel (c.symm v)
  have hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) :=
    chart_mem_atlas NativeModel (c.symm v)
  have hdreg : RegularRelativeCharts.Abelian.RelativeCharts.HasRegularCoordinates d := hd.2
  have hvD : v ∈ c.target ∩ c.symm ⁻¹' d.source :=
    ⟨hv, mem_chart_source NativeModel (c.symm v)⟩
  have hD : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
    c.isOpen_inter_preimage_symm d.open_source
  have h := ((hdreg.contDiffOn c.symm c.target hc).restrict_scalars ℝ).contDiffAt
    (hD.mem_nhds hvD)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_target.mpr
  refine ⟨c.symm.continuousAt hv, ?_⟩
  simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def, id_eq]
    using h.contMDiffAt

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticAffineCharts.Abelian.RelativeCharts
