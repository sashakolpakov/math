import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicPullback

/-! # Holomorphic Form Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicFormPullback

noncomputable section

/-! # Pullback of the original analytic differential forms

The chain rule for the genuine scheme-point map preserves the original
chart-evaluation relations. Pullback therefore descends to the original
holomorphic-form quotient, retaining its infinitesimal derivative definition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The coordinate expression of the actual scheme-point map in the original charts. -/
def originalSchemeChartMap (f : X ⟶ Y) (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y) :
    (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) → (Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) :=
  fun w => (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t)
    (ComplexPoint.Basic.Point.map f ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm w))

/-- The open domain where both original charts used for a scheme map are valid. -/
def originalSchemeChartDomain (f : X ⟶ Y) (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y) :
    Set (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) :=
  (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).target ∩
    (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm ⁻¹'
      (ComplexPoint.Basic.Point.map f ⁻¹' (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).source)

theorem isOpen_originalSchemeChartDomain (f : X ⟶ Y)
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y) :
    IsOpen (originalSchemeChartDomain f z t) := by
  have hmap : Continuous (ComplexPoint.Basic.Point.map f) := (ComplexPoint.Basic.Point.continuousMap f).continuous
  simp only [originalSchemeChartDomain, extChartAt_target, extChartAt_source,
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id,
    Set.preimage_id, ModelWithCorners.range_eq_univ, Set.inter_univ]
  exact (chartAt (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).isOpen_inter_preimage_symm
      (hmap.isOpen_preimage _
        (chartAt (Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).open_source)

theorem contDiffOn_originalSchemeChartMap (f : X ⟶ Y)
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y) :
    ContDiffOn ℂ ω (originalSchemeChartMap f z t) (originalSchemeChartDomain f z t) := by
  have hX : chartAt (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z = ComplexPoint.Basic.ComplexSchemePoint.localChart X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) z := rfl
  have hY : chartAt (Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t = ComplexPoint.Basic.ComplexSchemePoint.localChart Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) t := rfl
  simp only [originalSchemeChartDomain, extChartAt,
    OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, hX, hY]
  exact SchemeHolomorphic.contDiffOn_schemeMap_originalCharts f z t

theorem originalSchemeChartMap_mem_sectionDomain (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y)
    {w : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ}
    (hw : w ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z)
    (ht : ComplexPoint.Basic.Point.map f ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm w) ∈
      (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).source) :
    originalSchemeChartMap f z t w ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t := by
  refine ⟨(extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).map_source ht, ?_⟩
  change (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).symm
    (originalSchemeChartMap f z t w) ∈ U
  rw [originalSchemeChartMap,
    (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).left_inv ht]
  exact hw.2

/-- In valid charts, pullback of a function is its coordinate expression composed with the map. -/
theorem chartSection_originalFunctionPullback (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y)
    (g : ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U))
    {w : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ}
    (hw : w ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z)
    (ht : ComplexPoint.Basic.Point.map f ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm w) ∈
      (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).source) :
    ComplexPoint.Basic.ComplexSchemePoint.chartSection X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z
        (HolomorphicPullback.originalHolomorphicFunctionPullback f U g) w =
      ComplexPoint.Basic.ComplexSchemePoint.chartSection Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t g (originalSchemeChartMap f z t w) := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z _ hw,
    HolomorphicPullback.originalHolomorphicFunctionPullback_apply,
    ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) _ t g
      (originalSchemeChartMap_mem_sectionDomain f U z t hw ht)]
  apply congrArg g.1
  apply Subtype.ext
  exact ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).left_inv ht).symm

/-- The actual chain rule for the covectors defining the original holomorphic forms. -/
theorem chartSectionDifferential_originalFunctionPullback (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y)
    (g : ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U))
    {w : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ}
    (hw : w ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z)
    (ht : ComplexPoint.Basic.Point.map f ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm w) ∈
      (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).source) :
    ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z
        (HolomorphicPullback.originalHolomorphicFunctionPullback f U g) w =
      (ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t g
        (originalSchemeChartMap f z t w)).comp
          (fderiv ℂ (originalSchemeChartMap f z t) w) := by
  have htw := originalSchemeChartMap_mem_sectionDomain f U z t hw ht
  have hmap : DifferentiableAt ℂ (originalSchemeChartMap f z t) w :=
    (((contDiffOn_originalSchemeChartMap f z t) w ⟨hw.1, ht⟩).contDiffAt
      ((isOpen_originalSchemeChartDomain f z t).mem_nhds ⟨hw.1, ht⟩)).differentiableAt (by simp)
  have hg : DifferentiableAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.chartSection Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t g)
      (originalSchemeChartMap f z t w) :=
    ((ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffWithinAt Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t g htw).contDiffAt
      ((ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t).mem_nhds htw)).differentiableAt (by simp)
  have heq : Filter.EventuallyEq (𝓝 w)
      (ComplexPoint.Basic.ComplexSchemePoint.chartSection X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z
        (HolomorphicPullback.originalHolomorphicFunctionPullback f U g))
      (ComplexPoint.Basic.ComplexSchemePoint.chartSection Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t g ∘ originalSchemeChartMap f z t) := by
    filter_upwards [
      (ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
        (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z).mem_nhds hw,
      (isOpen_originalSchemeChartDomain f z t).mem_nhds ⟨hw.1, ht⟩] with v hv hvt
    exact chartSection_originalFunctionPullback f U z t g hv hvt.2
  rw [ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential, ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential,
    fderivWithin_of_isOpen (ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z) hw,
    fderivWithin_of_isOpen (ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) _ t) htw,
    heq.fderiv_eq]
  exact fderiv_comp w hg hmap

/-- Evaluation of actual pullback is pullback of the alternating form by the actual derivative. -/
theorem chartEvaluation_originalKahlerFormPullback (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (z : ComplexPoint.Basic.ComplexSchemePoint X) (t : ComplexPoint.Basic.ComplexSchemePoint Y)
    (p : ℕ) (θ : Algebra.DeRham.Basic.Form ℂ
      (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U)) p)
    {w : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ}
    (hw : w ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z)
    (ht : ComplexPoint.Basic.Point.map f ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm w) ∈
      (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).source) :
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z p
        (HolomorphicPullback.originalKahlerFormPullback f U p θ) w =
      (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t p θ
        (originalSchemeChartMap f z t w)).compContinuousLinearMap
          (fderiv ℂ (originalSchemeChartMap f z t) w) := by
  have htw := originalSchemeChartMap_mem_sectionDomain f U z t hw ht
  induction θ using Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      rw [HolomorphicPullback.originalKahlerFormPullback, Algebra.DeRham.Basic.map_mk,
        ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z p _ _ hw,
        ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) _ t p a₀ v htw]
      simp only [ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation]
      rw [chartSection_originalFunctionPullback f U z t a₀ hw ht]
      have hd : (fun j => ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
          (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) z
          (HolomorphicPullback.originalHolomorphicFunctionPullback f U (v j)) w) =
          (fun j => (ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) t
            (v j) (originalSchemeChartMap f z t w)).comp
              (fderiv ℂ (originalSchemeChartMap f z t) w)) := by
        funext j
        exact chartSectionDifferential_originalFunctionPullback f U z t (v j) hw ht
      rw [hd, Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_compContinuousLinearMap,
        Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.smul_compContinuousLinearMap]
  | zero =>
      rw [map_zero, ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero]
      exact ContinuousAlternatingMap.ext fun v => by
        simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  | add a b ha hb =>
      simp only [map_add, Pi.add_apply, ha, hb,
        Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.add_compContinuousLinearMap]
  | smul c a ha =>
      simp only [map_smul, Pi.smul_apply, ha,
        Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.smul_compContinuousLinearMap]

/-- Actual pullback preserves exactly the relations imposed in the original form quotient. -/
theorem originalKahlerFormPullback_mem_chartEvaluationKernel (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (p : ℕ)
    {θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U)) p}
    (hθ : θ ∈ ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) p) :
    HolomorphicPullback.originalKahlerFormPullback f U p θ ∈
      ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) p := by
  refine (ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ p _).2 fun z w hw => ?_
  let t := ComplexPoint.Basic.Point.map f ((extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) z).symm w)
  have ht : t ∈ (extChartAt 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) t).source := mem_extChartAt_source t
  rw [chartEvaluation_originalKahlerFormPullback f U z t p θ hw ht,
    (ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) _ p θ).1 hθ t _
      (originalSchemeChartMap_mem_sectionDomain f U z t hw ht)]
  exact ContinuousAlternatingMap.ext fun v => by
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Pullback on the unchanged original quotient of analytic holomorphic forms. -/
def originalHolomorphicFormPullback (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) p →ₗ[ℂ]
      ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) p :=
  (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) p).liftQ
    ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) p).mkQ.comp
      (HolomorphicPullback.originalKahlerFormPullback f U p)) (by
        intro θ hθ
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact originalKahlerFormPullback_mem_chartEvaluationKernel f U p hθ)

/-- Exterior differentiation commutes with pullback on the original form quotient. -/
theorem originalHolomorphicFormPullback_differential (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) p) :
    originalHolomorphicFormPullback f U (p + 1)
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) p θ) =
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U)) p
        (originalHolomorphicFormPullback f U p θ) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) p) θ
  change Submodule.Quotient.mk
    (HolomorphicPullback.originalKahlerFormPullback f U (p + 1) (Algebra.DeRham.Basic.differential ℂ _ p a)) =
    Submodule.Quotient.mk (Algebra.DeRham.Basic.differential ℂ _ p (HolomorphicPullback.originalKahlerFormPullback f U p a))
  rw [HolomorphicPullback.originalKahlerFormPullback_differential]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicFormPullback
