import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerEmbedding
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionComplementDimension

/-! # Stratum Layer Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerNormalPair

noncomputable section

/-!
# Actual normal pairs for the layers of an analytic support filtration

The closed layer embedding and its injective native derivative give genuine
normal coordinates. The full layer is the zero normal slice in these
coordinates. Its normal dimension is forced by the source and target models,
including the strict codimension bound for singular-boundary strata.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

namespace IntegralSmoothGeometricStratification

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {S : Set X}
variable (Q : IntegralSmoothStratification.IntegralSmoothGeometricStratification f S) [IsIntegral X] [Smooth f]

local instance : IsIntegral (Over.mk f).left := ‹IsIntegral X›
local instance : Smooth (Over.mk f).hom := ‹Smooth f›

local notation "AmbientModel" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension f) → ℂ)

local instance : ChartedSpace AmbientModel (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk f) ‹IsIntegral X› ‹Smooth f›

local instance (r : ℕ∞ω) : IsManifold (𝓘(ℂ, AmbientModel)) r
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk f) ‹IsIntegral X› ‹Smooth f› r

/-- The actual layer inclusion is a complex analytic immersion. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayer_isImmersionAt (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    Manifold.IsImmersionAt (𝓘(ℂ, (Q.analyticFiltrationPiece i).analyticModel))
      (𝓘(ℂ, AmbientModel)) ω (Q.analyticFiltrationLayerInclusion i) x :=
  ComplexPoints.Analytic.ImmersionNormalForm.isImmersionAt_of_injective_mfderiv (Q.analyticFiltrationLayerInclusion i) x
    (Q.contMDiff_analyticFiltrationLayerInclusion i ω x)
    (Q.mfderiv_analyticFiltrationLayerInclusion_injective i x)

/-- The complex complement selected by the proved immersion normal form. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.AnalyticFiltrationLayerChartComplement (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :=
  (Q.analyticFiltrationLayer_isImmersionAt i x).complement

/-- Genuine normal coordinates for the full closed layer in its actual
ambient open complement. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerNormalPair (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Q.analyticFiltrationPiece i).analyticModel
      (Q.AnalyticFiltrationLayerChartComplement i x) (Q.analyticFiltrationLayerInclusion i) x :=
  ComplexPoints.Analytic.NormalPairRecenter.immersionNormalPair (Q.analyticFiltrationLayer_isImmersionAt i x)
    (Q.isClosedEmbedding_analyticFiltrationLayerInclusion i).isEmbedding

/-- These coordinates identify the literal relative support layer with
the zero normal coordinate plane. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerNormalPair_mem_layer (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace)
    (y : (Q.analyticFiltrationLayerNormalPair i x).neighborhood) :
    y.val ∈ ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
        (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ) ↔
      ((Q.analyticFiltrationLayerNormalPair i x).homeomorph y).2.val = 0 := by
  rw [← Q.range_analyticFiltrationLayerInclusion i]
  exact (Q.analyticFiltrationLayerNormalPair i x).mem_range_iff y

/-- The normal pair describes the full layer, including all source points,
as an exact equality of coordinate images. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerNormalPair_image_layer (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    (Q.analyticFiltrationLayerNormalPair i x).ambientChart ''
      ((Q.analyticFiltrationLayerNormalPair i x).neighborhood ∩
        ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk f)))
          (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ)) =
      Metric.ball (0 : (Q.analyticFiltrationPiece i).analyticModel)
        (Q.analyticFiltrationLayerNormalPair i x).radius ×ˢ
          ({0} : Set (Q.AnalyticFiltrationLayerChartComplement i x)) := by
  rw [← Q.range_analyticFiltrationLayerInclusion i]
  exact (Q.analyticFiltrationLayerNormalPair i x).ambientChart_image_support

/-- The actual normal complement is finite dimensional. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerChartComplement_finiteDimensional
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    FiniteDimensional ℂ (Q.AnalyticFiltrationLayerChartComplement i x) :=
  ComplexPoints.Analytic.ImmersionComplementDimension.immersionComplement_finiteDimensional (Q.analyticFiltrationLayer_isImmersionAt i x)

/-- The complex normal dimension is exactly ambient dimension minus the
actual dimension of the original smooth piece. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerChartComplement_complex_finrank
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    Module.finrank ℂ (Q.AnalyticFiltrationLayerChartComplement i x) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension f -
        (Q.analyticFiltrationPiece i).complexDimension := by
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    ComplexPoints.Analytic.ImmersionComplementDimension.immersionComplement_finrank (Q.analyticFiltrationLayer_isImmersionAt i x)

/-- The real normal dimension is twice the derived complex codimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerChartComplement_real_finrank
    (i : Fin Q.analyticSupportList.length) (x : (Q.analyticFiltrationPiece i).analyticSpace) :
    Module.finrank ℝ (Q.AnalyticFiltrationLayerChartComplement i x) =
      2 * (Betti.AffineDimension.Realization.functionFieldDifferentialDimension f -
        (Q.analyticFiltrationPiece i).complexDimension) := by
  let := Q.analyticFiltrationLayerChartComplement_finiteDimensional i x
  rw [finrank_real_of_complex, Q.analyticFiltrationLayerChartComplement_complex_finrank i x]

/-- Actual normal coordinates can be shrunk inside every neighborhood of
the layer point without changing the coordinate map. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification.analyticFiltrationLayerNormalPair_cofinal (i : Fin Q.analyticSupportList.length)
    (x : (Q.analyticFiltrationPiece i).analyticSpace)
    (U : Set (Q.analyticFiltrationComplement i))
    (hU : U ∈ 𝓝 (Q.analyticFiltrationLayerInclusion i x)) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Q.analyticFiltrationPiece i).analyticModel
        (Q.AnalyticFiltrationLayerChartComplement i x) (Q.analyticFiltrationLayerInclusion i) x,
      P.ambientChart = (Q.analyticFiltrationLayerNormalPair i x).ambientChart ∧
        P.neighborhood ⊆ U :=
  (Q.analyticFiltrationLayerNormalPair i x).exists_subpair U hU

end IntegralSmoothGeometricStratification

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Every actual singular-boundary layer has complex normal dimension at
least one greater than the codimension of the original support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerChartComplement_complex_finrank_ge
    (Z : DimensionCycles.DimensionCycleSupport V p)
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (x : (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticSpace) :
    p + 1 ≤ Module.finrank ℂ
      (Z.singularBoundaryStratification.AnalyticFiltrationLayerChartComplement i x) := by
  rw [Z.singularBoundaryStratification.analyticFiltrationLayerChartComplement_complex_finrank i x]
  have h := Z.singularBoundaryClosedFiltration_piece_codimension i
  change p + 1 ≤ V.complexDimension -
    (Z.singularBoundaryStratification.analyticFiltrationPiece i).complexDimension
  omega

/-- Thus the actual real normal dimension is at least `2*(p+1)`, the
codimension bound needed for both singular-extension obstruction degrees. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerChartComplement_real_finrank_ge
    (Z : DimensionCycles.DimensionCycleSupport V p)
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (x : (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticSpace) :
    2 * (p + 1) ≤ Module.finrank ℝ
      (Z.singularBoundaryStratification.AnalyticFiltrationLayerChartComplement i x) := by
  rw [Z.singularBoundaryStratification.analyticFiltrationLayerChartComplement_real_finrank i x]
  have h := Z.singularBoundaryClosedFiltration_piece_codimension i
  change 2 * (p + 1) ≤ 2 * (V.complexDimension -
    (Z.singularBoundaryStratification.analyticFiltrationPiece i).complexDimension)
  omega

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerNormalPair
