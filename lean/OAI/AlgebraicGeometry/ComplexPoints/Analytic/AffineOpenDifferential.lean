import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Affine Open Differential -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

noncomputable section

/-!
# Differentials of genuine affine open immersions

An actual affine open immersion is a smooth map from the smooth-domain
character manifold to the native scheme-point manifold. Its derivative is
bijective: lifting an affine chart through the immersion gives a chart whose
transitions with the native atlas are analytic in both directions.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry ChartedSpace

section Euclidean

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
/-- A differentiable open partial homeomorphism with differentiable inverse
has bijective ordinary derivative at every point of its source. -/
theorem bijective_fderiv_openPartialHomeomorph (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn 𝕜 1 e e.source) (he' : ContDiffOn 𝕜 1 e.symm e.target)
    {x : E} (hx : x ∈ e.source) : Function.Bijective (fderiv 𝕜 e x) := by
  have h : e.MDifferentiable (𝓘(𝕜, E)) (𝓘(𝕜, F)) := by
    constructor
    · exact mdifferentiableOn_iff_differentiableOn.mpr (he.differentiableOn one_ne_zero)
    · exact mdifferentiableOn_iff_differentiableOn.mpr (he'.differentiableOn one_ne_zero)
  simpa only [mfderiv_eq_fderiv, TangentSpace] using h.mfderiv_bijective hx

end Euclidean

section Charts

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An affine point map has analytic coordinate expressions in the native
regular atlas, with any regular source chart. -/
theorem contDiffOn_affinePointMap_regularCharts (A : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) {n m : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (d : OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas A n) (hd : d ∈ IntrinsicSmoothSchemeManifold.schemeRegularAtlas X m) :
    ContDiffOn ℂ ω
      (fun z => d (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z)))
      (e.target ∩ {z | SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈ d.source}) := by
  obtain ⟨V, hV, f, hf, rfl⟩ := hd
  exact IntrinsicSmoothSchemeMaps.contDiffOn_affineMap_regularCharts A (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
    i (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) e f he hf

/-- In arbitrary regular coordinates, an actual affine open immersion has
bijective complex and real ordinary derivatives. -/
theorem fderiv_affineOpenPointMap_charts_bijective (A : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] {n m : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (d : OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X) (Fin m → ℂ))
    (he : e ∈ SmoothSchemeManifold.affineRegularAtlas A n) (hd : d ∈ IntrinsicSmoothSchemeManifold.schemeRegularAtlas X m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)
    (hdx : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ∈ d.source) :
    Function.Bijective (fderiv ℂ
      (fun z => d (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e x)) ∧
    Function.Bijective (fderiv ℝ
      (fun z => d (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e x)) := by
  obtain ⟨V, hV, f, hf, rfl⟩ := hd
  let B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let j := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  let T := (SmoothSchemeManifold.affineChartOnScheme A i e).symm.trans (SmoothSchemeManifold.affineChartOnScheme B j f)
  have hT : ContDiffOn ℂ 1 T T.source :=
    (AffineOpenTransitions.contDiffOn_affineOpenChartTransition A B i j e f he hf).of_le (by simp)
  have hT' : ContDiffOn ℂ 1 T.symm T.target := by
    change ContDiffOn ℂ 1
      ((SmoothSchemeManifold.affineChartOnScheme B j f).symm.trans (SmoothSchemeManifold.affineChartOnScheme A i e))
      ((SmoothSchemeManifold.affineChartOnScheme B j f).symm.trans (SmoothSchemeManifold.affineChartOnScheme A i e)).source
    exact (AffineOpenTransitions.contDiffOn_affineOpenChartTransition B A j i f e hf he).of_le (by simp)
  have hTx : e x ∈ T.source := by
    refine ⟨e.map_source hx, ?_⟩
    change SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm (e x)) ∈
      (SmoothSchemeManifold.affineChartOnScheme B j f).source
    rw [e.left_inv hx]
    exact hdx
  exact ⟨bijective_fderiv_openPartialHomeomorph T hT hT' hTx,
    bijective_fderiv_openPartialHomeomorph T
      (hT.restrict_scalars ℝ) (hT'.restrict_scalars ℝ) hTx⟩

end Charts

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
variable (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]

local notation "ModelA" => (Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- A genuine affine scheme map induces an analytic map from its smooth-domain
point manifold to the native target manifold. -/
theorem contMDiff_affinePointMap (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelA)) (𝓘(ℂ, ModelX)) r (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) := by
  apply contMDiff_iff.mpr
  refine ⟨SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using (contDiffOn_affinePointMap_regularCharts A i
      (chartAt ModelA x) (chartAt ModelX y)
      (chart_mem_atlas _ x) (chart_mem_atlas _ y)).of_le (show r ≤ ω from le_top)

/-- The same genuine affine scheme map is smooth for the underlying real
manifolds. -/
theorem real_contMDiff_affinePointMap (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, ModelA)) (𝓘(ℝ, ModelX)) r (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) := by
  apply contMDiff_iff.mpr
  refine ⟨SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i, ?_⟩
  intro x y
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using ((contDiffOn_affinePointMap_regularCharts A i
      (chartAt ModelA x) (chartAt ModelX y)
      (chart_mem_atlas _ x) (chart_mem_atlas _ y)).of_le
        (show r ≤ ω from le_top)).restrict_scalars ℝ

set_option backward.isDefEq.respectTransparency false in
/-- The complex manifold derivative of an affine point map is its ordinary
derivative in the constructed preferred charts. -/
theorem mfderiv_affinePointMap_eq_chart_fderiv (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    mfderiv (𝓘(ℂ, ModelA)) (𝓘(ℂ, ModelX)) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x =
      fderiv ℂ (fun z => chartAt ModelX (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)
        (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i ((chartAt ModelA x).symm z)))
        (chartAt ModelA x x) := by
  rw [((contMDiff_affinePointMap A i 1).mdifferentiableAt (x := x) one_ne_zero).mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]

set_option backward.isDefEq.respectTransparency false in
/-- The analogous chart formula for the real manifold derivative. -/
theorem real_mfderiv_affinePointMap_eq_chart_fderiv (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    mfderiv (𝓘(ℝ, ModelA)) (𝓘(ℝ, ModelX)) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x =
      fderiv ℝ (fun z => chartAt ModelX (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)
        (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i ((chartAt ModelA x).symm z)))
        (chartAt ModelA x x) := by
  rw [((real_contMDiff_affinePointMap A i 1).mdifferentiableAt
    (x := x) one_ne_zero).mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]

/-- Every actual affine open immersion has bijective complex differential
between the established affine and native scheme-point manifolds. -/
theorem mfderiv_affinePointMap_bijective (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    [IsOpenImmersion i.left] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Function.Bijective
      (mfderiv (𝓘(ℂ, ModelA)) (𝓘(ℂ, ModelX)) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x) := by
  rw [mfderiv_affinePointMap_eq_chart_fderiv]
  exact (fderiv_affineOpenPointMap_charts_bijective A i
    (chartAt ModelA x) (chartAt ModelX (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x))
    (chart_mem_atlas _ x) (chart_mem_atlas _ _) x
    (mem_chart_source _ x) (mem_chart_source _ _)).1

/-- The underlying real differential of an actual affine open immersion is
also bijective. -/
theorem real_mfderiv_affinePointMap_bijective (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    [IsOpenImmersion i.left] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Function.Bijective
      (mfderiv (𝓘(ℝ, ModelA)) (𝓘(ℝ, ModelX)) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x) := by
  rw [real_mfderiv_affinePointMap_eq_chart_fderiv]
  exact (fderiv_affineOpenPointMap_charts_bijective A i
    (chartAt ModelA x) (chartAt ModelX (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x))
    (chart_mem_atlas _ x) (chart_mem_atlas _ _) x
    (mem_chart_source _ x) (mem_chart_source _ _)).2

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
