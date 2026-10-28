import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticAffineCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

/-! # Analytic Intrinsic Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticIntrinsicCharts.Abelian.RelativeCharts

noncomputable section

/-!
Lift the constructed regular-evaluation charts to the actual native smooth
scheme manifold. The chart and inverse are complex and real smooth, with
bijective differentials. This supplies actual tangent identifications for
the sliced fiber charts used in the relative exponential comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential ChartedSpace Set
open scoped Classical ContDiff _root_.Manifold _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem contDiffOn_schemeRegular_to_affineChart
    (B : CommAlgCat ℂ) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E) (he : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates e)
    {n : ℕ} (d : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ))
    (hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) :
    ContDiffOn ℂ ω (fun z => AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e (d.symm z))
      (d.target ∩ d.symm ⁻¹' (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).source) := by
  obtain ⟨U, hU, a, ha, rfl⟩ := hd
  exact AnalyticSchemeFamilies.Abelian.RelativeCharts.contDiffOn_schemeImage_in_affineChart
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) B
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) i e he
    a.symm a.target a.open_target ha.1

variable [IsIntegral X.left] [Smooth X.hom]

local notation "NativeModel" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

theorem nativeAffineChart_contMDiffOn
    (B : CommAlgCat ℂ) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E) (he : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates e) :
    ContMDiffOn (𝓘(ℂ, NativeModel)) (𝓘(ℂ, E)) ω
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e) (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).source := by
  intro x hx
  let c := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e
  let d := chartAt NativeModel x
  have hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) :=
    chart_mem_atlas NativeModel x
  have hxD : d x ∈ d.target ∩ d.symm ⁻¹' c.source :=
    ⟨d.map_source (mem_chart_source NativeModel x), by
      change d.symm (d x) ∈ c.source
      rw [d.left_inv (mem_chart_source NativeModel x)]
      exact hx⟩
  have hD : IsOpen (d.target ∩ d.symm ⁻¹' c.source) :=
    d.isOpen_inter_preimage_symm c.open_source
  have h := (contDiffOn_schemeRegular_to_affineChart B i e he d hd).contDiffAt (hD.mem_nhds hxD)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id]
    using h.contMDiffAt.contMDiffWithinAt (s := (univ : Set NativeModel))

theorem nativeAffineChart_symm_contMDiffOn
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E)
    (he : ∀ b : B, ContDiffOn ℂ ω (fun z => e.symm z b) e.target) :
    ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, NativeModel)) ω
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).symm (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).target :=
  (AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap B i ω).comp_contMDiffOn (AnalyticAffineCharts.Abelian.RelativeCharts.inverseRegular_contMDiffOn e he)

theorem nativeAffineChart_mfderiv_bijective
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E) (he : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates e)
    (hi : ∀ b : B, ContDiffOn ℂ ω (fun z => e.symm z b) e.target)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : x ∈ (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).source) :
    Function.Bijective (mfderiv (𝓘(ℂ, NativeModel)) (𝓘(ℂ, E)) (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e) x) := by
  have hmd : (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).MDifferentiable (𝓘(ℂ, NativeModel)) (𝓘(ℂ, E)) :=
    ⟨(nativeAffineChart_contMDiffOn B i e he).mdifferentiableOn (by simp),
      (nativeAffineChart_symm_contMDiffOn B i e hi).mdifferentiableOn (by simp)⟩
  exact hmd.mfderiv_bijective hx

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem nativeAffineChart_real_contMDiffOn
    (B : CommAlgCat ℂ) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E) (he : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates e) :
    ContMDiffOn (𝓘(ℝ, NativeModel)) (𝓘(ℝ, E)) ω
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e) (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).source := by
  intro x hx
  let c := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e
  let d := chartAt NativeModel x
  have hd : d ∈ AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) :=
    chart_mem_atlas NativeModel x
  have hxD : d x ∈ d.target ∩ d.symm ⁻¹' c.source :=
    ⟨d.map_source (mem_chart_source NativeModel x), by
      change d.symm (d x) ∈ c.source
      rw [d.left_inv (mem_chart_source NativeModel x)]
      exact hx⟩
  have hD : IsOpen (d.target ∩ d.symm ⁻¹' c.source) :=
    d.isOpen_inter_preimage_symm c.open_source
  have h := ((contDiffOn_schemeRegular_to_affineChart B i e he d hd).restrict_scalars ℝ).contDiffAt
    (hD.mem_nhds hxD)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id]
    using h.contMDiffAt.contMDiffWithinAt (s := (univ : Set NativeModel))

theorem nativeAffineChart_symm_real_contMDiffOn
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E)
    (he : ∀ b : B, ContDiffOn ℂ ω (fun z => e.symm z b) e.target) :
    ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, NativeModel)) ω
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).symm (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).target :=
  (AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential.real_contMDiff_affinePointMap B i ω).comp_contMDiffOn (AnalyticAffineCharts.Abelian.RelativeCharts.inverseRegular_real_contMDiffOn e he)

theorem nativeAffineChart_real_mfderiv_bijective
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E) (he : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates e)
    (hi : ∀ b : B, ContDiffOn ℂ ω (fun z => e.symm z b) e.target)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : x ∈ (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).source) :
    Function.Bijective (mfderiv (𝓘(ℝ, NativeModel)) (𝓘(ℝ, E)) (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e) x) := by
  have hmd : (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart B i e).MDifferentiable (𝓘(ℝ, NativeModel)) (𝓘(ℝ, E)) :=
    ⟨(nativeAffineChart_real_contMDiffOn B i e he).mdifferentiableOn (by simp),
      (nativeAffineChart_symm_real_contMDiffOn B i e hi).mdifferentiableOn (by simp)⟩
  exact hmd.mfderiv_bijective hx

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticIntrinsicCharts.Abelian.RelativeCharts
