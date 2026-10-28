import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicFormPullback
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Cotangent Evaluation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentEvaluation

noncomputable section

/-! # Original holomorphic forms as actual complex tangent covectors

Evaluation at each point in its actual preferred chart gives a complex tangent
covector. The original relations are exactly the kernel of this evaluation:
the chain rule for genuine chart transitions detects all chart values from the
preferred value. Thus the original holomorphic-form quotient embeds faithfully
into actual tangent covector fields, rather than into unrelated abstract data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "I" => 𝓘(ℂ, E)

/-- Actual complex cotangent fields on the original analytic open. -/
abbrev OriginalComplexCotangentField (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :=
  ∀ x : U, TangentSpace I x.val [⋀^Fin p]→L[ℂ] ℂ

/-- Evaluation in each point's genuine preferred coordinates. -/
def originalKahlerCotangentEvaluation (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :
    Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p →ₗ[ℂ]
      OriginalComplexCotangentField X U p where
  toFun θ x := ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) x.val p
    (extChartAt I x.val x.val) θ
  map_add' θ η := by
    funext x
    exact (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) x.val p
      (extChartAt I x.val x.val)).map_add θ η
  map_smul' c θ := by
    funext x
    exact (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationAt X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) x.val p
      (extChartAt I x.val x.val)).map_smul c θ

theorem originalHolomorphicFunctionPullback_identity
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) :
    HolomorphicPullback.originalHolomorphicFunctionPullback (𝟙 X) U = AlgHom.id ℂ _ := by
  apply AlgHom.ext
  intro g
  exact ContMDiffMap.ext fun _ => rfl

theorem chartSectionDifferential_change_chart
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (g : ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U))
    (z t : ComplexPoint.Basic.ComplexSchemePoint X) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z)
    (ht : (extChartAt I z).symm y ∈ (extChartAt I t).source) :
    ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z g y =
      (ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) t g
        (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t y)).comp
          (fderiv ℂ (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t) y) := by
  have h := HolomorphicFormPullback.chartSectionDifferential_originalFunctionPullback (𝟙 X) U z t g hy ht
  rw [originalHolomorphicFunctionPullback_identity] at h
  exact h

theorem chartEvaluation_change_chart
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p)
    (z t : ComplexPoint.Basic.ComplexSchemePoint X) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z)
    (ht : (extChartAt I z).symm y ∈ (extChartAt I t).source) :
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ y =
      (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) t p θ
        (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t y)).compContinuousLinearMap
          (fderiv ℂ (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t) y) := by
  have hty := HolomorphicFormPullback.originalSchemeChartMap_mem_sectionDomain (𝟙 X) U z t hy ht
  induction θ using Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      rw [ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z p _ _ hy,
        ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ t p a₀ v hty]
      simp only [ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation]
      have hf := HolomorphicFormPullback.chartSection_originalFunctionPullback (𝟙 X) U z t a₀ hy ht
      rw [originalHolomorphicFunctionPullback_identity] at hf
      have hf' : ComplexPoint.Basic.ComplexSchemePoint.chartSection X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z a₀ y =
          ComplexPoint.Basic.ComplexSchemePoint.chartSection X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) t a₀
            (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t y) := hf
      rw [hf']
      have hd : (fun j => ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z
          (v j) y) =
          (fun j => (ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) t
            (v j) (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t y)).comp
              (fderiv ℂ (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t) y)) := by
        funext j
        exact chartSectionDifferential_change_chart X U (v j) z t hy ht
      rw [hd, Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_compContinuousLinearMap,
        Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.smul_compContinuousLinearMap]
  | zero =>
      rw [ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero, ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero]
      exact ContinuousAlternatingMap.ext fun _ => rfl
  | add a b ha hb =>
      simp only [map_add, Pi.add_apply, ha, hb,
        Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.add_compContinuousLinearMap]
  | smul c a ha =>
      simp only [map_smul, Pi.smul_apply, ha,
        Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.smul_compContinuousLinearMap]

/-- Actual chart evaluation is determined by the preferred tangent value at that point. -/
theorem chartEvaluation_eq_cotangentEvaluation
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p)
    (z : ComplexPoint.Basic.ComplexSchemePoint X) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z) :
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ y =
      (originalKahlerCotangentEvaluation X U p θ
        ⟨(extChartAt I z).symm y, hy.2⟩).compContinuousLinearMap
          (fderiv ℂ (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z ((extChartAt I z).symm y)) y) := by
  let t := (extChartAt I z).symm y
  have h := chartEvaluation_change_chart X U p θ z t hy
    (mem_extChartAt_source t)
  exact h

/-- The original quotient kills exactly those forms whose actual tangent field is zero. -/
theorem originalKahlerCotangentEvaluation_kernel
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :
    LinearMap.ker (originalKahlerCotangentEvaluation X U p) =
      ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p := by
  ext θ
  rw [LinearMap.mem_ker, ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff]
  constructor
  · intro h z y hy
    rw [chartEvaluation_eq_cotangentEvaluation X U p θ z hy]
    have hx := congrFun h ⟨(extChartAt I z).symm y, hy.2⟩
    rw [hx]
    exact ContinuousAlternatingMap.ext fun _ => rfl
  · intro h
    funext x
    exact h x.val (extChartAt I x.val x.val)
      ⟨(extChartAt I x.val).map_source (mem_extChartAt_source x.val),
        by
          change (extChartAt I x.val).symm (extChartAt I x.val x.val) ∈ U
          rw [(extChartAt I x.val).left_inv (mem_extChartAt_source x.val)]
          exact x.property⟩

/-- Faithful evaluation of the unchanged original holomorphic-form quotient. -/
def originalHolomorphicCotangentEvaluation
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p →ₗ[ℂ]
      OriginalComplexCotangentField X U p :=
  (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).liftQ
    (originalKahlerCotangentEvaluation X U p)
    (originalKahlerCotangentEvaluation_kernel X U p).ge

theorem originalHolomorphicCotangentEvaluation_injective
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :
    Function.Injective (originalHolomorphicCotangentEvaluation X U p) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot'
    (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p)
    (originalKahlerCotangentEvaluation X U p)
    (originalKahlerCotangentEvaluation_kernel X U p).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentEvaluation
