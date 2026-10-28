import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Intrinsic Smooth Scheme Maps -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

noncomputable section

/-!
# Analyticity of actual morphisms of smooth complex schemes

Every morphism over the complex base induces its genuine map on scheme-valued
complex points. On overlapping affine charts it is described by an algebra
map into a principal localization. Its regular coordinate evaluations are
therefore analytic, yielding complex and real manifold smoothness.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry ChartedSpace

section AffineMap

variable {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An actual map from an affine complex scheme is analytic in regular source
coordinates and any regular chart on an affine open in the target. -/
theorem contDiffOn_affineMap_regularCharts (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    [IsOpenImmersion j.left] {n m : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas A n) (hf : f ∈ SmoothSchemeManifold.affineRegularAtlas B m) :
    ContDiffOn ℂ ω
      (fun z => SmoothSchemeManifold.affineChartOnScheme B j f (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z)))
      (e.target ∩ {z | SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈
        (SmoothSchemeManifold.affineChartOnScheme B j f).source}) := by
  let D := e.target ∩ {z | SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈
    (SmoothSchemeManifold.affineChartOnScheme B j f).source}
  have hD : IsOpen D := e.isOpen_inter_preimage_symm
    ((SmoothSchemeManifold.affineChartOnScheme B j f).open_source.preimage
      (SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i))
  apply contDiffOn_pi.mpr
  intro k z hz
  have hez : z ∈ e.target := hz.1
  have hzimage : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source := hz.2
  obtain ⟨y, hy, hxy⟩ := hzimage
  obtain ⟨a, ha, h, _hfac, hpoint⟩ :=
    SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j (e.symm z) ⟨y, hxy⟩
  let v : (Fin n → ℂ) → B → ℂ := fun w b =>
    e.symm w (IsLocalization.Away.sec a (h b)).1 /
      (e.symm w a) ^ (IsLocalization.Away.sec a (h b)).2
  have hval (w : Fin n → ℂ) (hw : e.symm w a ≠ 0) (b : B) :
      SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h ⟨e.symm w, hw⟩ b =
        v w b :=
    SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_eval A B a h ⟨e.symm w, hw⟩ b
  have hvat (b : B) : ContDiffAt ℂ ω (fun w => v w b) z :=
    ((he.1 (IsLocalization.Away.sec a (h b)).1).contDiffAt
      (e.open_target.mem_nhds hez)).div
      (((he.1 a).contDiffAt (e.open_target.mem_nhds hez)).pow
        (IsLocalization.Away.sec a (h b)).2)
      (pow_ne_zero _ ha)
  have hqz : SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨e.symm z, ha⟩ = y :=
    (SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxy.symm)
  obtain ⟨g, hg, hcoords⟩ := hf.2
  obtain ⟨b, r, hcoord⟩ := hcoords k
  have hgz : v z g ≠ 0 := by
    rw [← hval z ha g, hqz]
    exact hg y hy
  have hquot := (hvat b).div ((hvat g).pow r) (pow_ne_zero r hgz)
  apply ContDiffAt.contDiffWithinAt
  apply hquot.congr_of_eventuallyEq
  have hna : ∀ᶠ w in 𝓝 z, e.symm w a ≠ 0 :=
    ((he.1 a).contDiffAt (e.open_target.mem_nhds hez)).continuousAt.eventually_ne ha
  filter_upwards [hD.mem_nhds hz, hna] with w hw hwa
  have hwimage : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm w) ∈
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source := hw.2
  obtain ⟨yw, hyw, hxyw⟩ := hwimage
  have hqw : SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨e.symm w, hwa⟩ = yw :=
    (SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint _).trans hxyw.symm)
  have hqsource : SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h
      ⟨e.symm w, hwa⟩ ∈ f.source := hqw.symm ▸ hyw
  rw [← hpoint ⟨e.symm w, hwa⟩, SmoothSchemeManifold.affineChartOnScheme_apply, hcoord _ hqsource,
    hval w hwa b, hval w hwa g]
  rfl

end AffineMap

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An actual scheme morphism is analytic between arbitrary members of the
proved native regular atlases on its source and target. -/
theorem contDiffOn_schemeMap_regularCharts (φ : X ⟶ Y) {n m : ℕ}
    (c : OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ))
    (d : OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints Y) (Fin m → ℂ))
    (hc : c ∈ IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) (hd : d ∈ IntrinsicSmoothSchemeManifold.schemeRegularAtlas Y m) :
    ContDiffOn ℂ ω (fun z => d (SchemePointHomeomorphs.schemeComplexPoints.map φ (c.symm z)))
      (c.target ∩ {z | SchemePointHomeomorphs.schemeComplexPoints.map φ (c.symm z) ∈ d.source}) := by
  obtain ⟨U, hU, e, he, rfl⟩ := hc
  obtain ⟨V, hV, f, hf, rfl⟩ := hd
  have htarget : (SmoothSchemeManifold.affineChartOnScheme (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e).target = e.target := rfl
  simpa only [SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, SmoothSchemeManifold.affineChartOnScheme_symm_apply,
    htarget] using
    contDiffOn_affineMap_regularCharts
      (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
      (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU ≫ φ)
      (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV) e f he hf

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- The map on native complex points is analytic in the preferred native
manifold charts. -/
theorem contDiffOn_nativeScheme_map_charts (φ : X ⟶ Y)
    (x : SchemePointHomeomorphs.schemeComplexPoints X) (y : SchemePointHomeomorphs.schemeComplexPoints Y) :
    ContDiffOn ℂ ω
      (fun z => chartAt ModelY y (SchemePointHomeomorphs.schemeComplexPoints.map φ ((chartAt ModelX x).symm z)))
      ((chartAt ModelX x).target ∩
        {z | SchemePointHomeomorphs.schemeComplexPoints.map φ ((chartAt ModelX x).symm z) ∈
          (chartAt ModelY y).source}) :=
  contDiffOn_schemeMap_regularCharts φ _ _
    (chart_mem_atlas ModelX x) (chart_mem_atlas ModelY y)

/-- Every actual morphism of integral smooth complex schemes induces an
analytic map on their constructed native complex-point manifolds. -/
theorem contMDiff_nativeScheme_map (φ : X ⟶ Y) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) r (SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  apply contMDiff_iff.mpr
  refine ⟨SchemePointHomeomorphs.schemeComplexPoints.continuous_map φ, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using (contDiffOn_nativeScheme_map_charts φ x y).of_le (show r ≤ ω from le_top)

/-- The same native morphism is smooth on the underlying real manifolds used
for complex-valued differential forms. -/
theorem real_contMDiff_nativeScheme_map (φ : X ⟶ Y) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) r (SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  apply contMDiff_iff.mpr
  refine ⟨SchemePointHomeomorphs.schemeComplexPoints.continuous_map φ, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using ((contDiffOn_nativeScheme_map_charts φ x y).of_le
      (show r ≤ ω from le_top)).restrict_scalars ℝ

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
