import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerNormalPair
import OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity
import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
import Mathlib.Topology.Metrizable.Urysohn

/-! # Singular Boundary Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SingularBoundaryPurity

noncomputable section

/-!
# Rational support cohomology of an algebraic cycle's singular boundary

The filtration is the actual closed analytic filtration constructed from a
finite algebraic stratification of the singular boundary. Each layer is the
image of its genuine smooth scheme piece in the complement of the preceding
stage. Its normal dimension follows from the strict dimension drop along the
boundary, rather than from an assumed cohomological purity premise.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity.Cycles
open scoped ContDiff _root_.Manifold _root_.Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : DimensionCycles.DimensionCycleSupport V p)

/-- Genuine relative rational cohomology with support in the actual analytic
singular boundary. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryRationalCohomology (n : ℕ) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
    Z.analyticSingularBoundaryᶜ n

/-- A layer is viewed in the actual open complement of the preceding stage. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerRationalCohomology
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (n : ℕ) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (Z.singularBoundaryStratification.analyticFiltrationComplement i))
    (ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of V.analyticSpace)
      (Z.singularBoundaryClosedFiltration i.castSucc)
      (Z.singularBoundaryClosedFiltration i.succ))ᶜ n

/-- The genuine relative layer equals the range of its smooth closed embedding. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerRationalCohomology_eq_range
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length) (n : ℕ) :
    Z.singularBoundaryLayerRationalCohomology i n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Z.singularBoundaryStratification.analyticFiltrationComplement i))
        (Set.range (Z.singularBoundaryStratification.analyticFiltrationLayerInclusion i))ᶜ
        n := by
  rw [Z.singularBoundaryStratification.range_analyticFiltrationLayerInclusion i]
  rfl

/-- Each actual layer has complex codimension at least one greater than the
original cycle support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayer_complexCodimension_ge
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length) :
    p + 1 ≤ V.complexDimension -
      (Z.singularBoundaryStratification.analyticFiltrationPiece i).complexDimension := by
  have h := Z.singularBoundaryClosedFiltration_piece_codimension i
  omega

/-- The dimension bound expressed in the native manifold model ranks used
by smooth support purity. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayer_realCodimension_ge
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length) :
    2 * (p + 1) ≤ 2 * (Module.finrank ℂ V.analyticModel -
      Module.finrank ℂ
        (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticModel) := by
  rw [V.analyticModel_complex_finrank,
    (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticModel_complex_finrank,
    ← (Z.singularBoundaryStratification.analyticFiltrationPiece i).complexDimension_eq_dimension]
  exact Nat.mul_le_mul_left 2 (Z.singularBoundaryLayer_complexCodimension_ge i)

/-- Every degree below the boundary codimension is below each layer's
actual real codimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayer_degree_lt_realCodimension
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (n : ℕ) (hn : n < 2 * (p + 1)) :
    n < 2 * (Module.finrank ℂ V.analyticModel -
      Module.finrank ℂ
        (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticModel) :=
  hn.trans_le (Z.singularBoundaryLayer_realCodimension_ge i)

/-- The actual ambient open complement is metrizable, by the proved compact
Hausdorff second-countable topology of the projective variety. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryFiltrationComplement_metrizable
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length) :
    MetrizableSpace (Z.singularBoundaryStratification.analyticFiltrationComplement i) := by
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) := by
    change MetrizableSpace V.analyticSpace
    infer_instance
  change MetrizableSpace
    ↥((Z.singularBoundaryClosedFiltration i.castSucc :
      Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)))ᶜ)
  infer_instance

/-- The actual finite support filtration transfers vanishing from all of its
actual layers to the singular boundary. The geometric layer proofs below
discharge this helper's inputs. -/
private theorem singularBoundaryRationalCohomology_isZero_of_layers
    (n : ℕ)
    (hLayer : ∀ i : Fin Z.singularBoundaryStratification.analyticSupportList.length,
      IsZero (Z.singularBoundaryLayerRationalCohomology i n)) :
    IsZero (Z.singularBoundaryRationalCohomology n) := by
  have hfirst : Z.singularBoundaryClosedFiltration 0 = ⊥ :=
    Z.singularBoundaryStratification.analyticClosedFiltration_zero
  have h := ClosedSupportFiltration.Cycles.closedSupportFiltration_isZero (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)))
    Z.singularBoundaryStratification.analyticSupportList.length
    Z.singularBoundaryClosedFiltration
    Z.singularBoundaryStratification.analyticClosedFiltration_monotone n
    (by
      simpa only [hfirst, Closeds.coe_bot] using
        (ClosedSupportFiltration.Cycles.cohomologyWithEmptySupport_isZero (ModuleCat.of ℚ ℚ)
          (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap))) n))
    (fun i => hLayer i)
  change IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap))) Z.analyticSingularBoundaryᶜ n)
  simpa only [Z.singularBoundaryClosedFiltration_last] using h

/-- Local rational cohomology in the constructed normal neighborhood of an
actual smooth boundary layer. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerLocalRationalCohomology
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (x : (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticSpace)
    (n : ℕ) : ModuleCat.{0} ℚ :=
  (Z.singularBoundaryStratification.analyticFiltrationLayerNormalPair i x).relativeCohomology
    (ModuleCat.of ℚ ℚ) n

/-- The computed local support cohomology of every actual boundary layer
vanishes throughout the required range. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerLocalRationalCohomology_isZero_of_lt
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (x : (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticSpace)
    (n : ℕ) (hn : n < 2 * (p + 1)) :
    IsZero (Z.singularBoundaryLayerLocalRationalCohomology i x n) := by
  let := Z.singularBoundaryStratification.analyticFiltrationLayerChartComplement_finiteDimensional
    i x
  apply (Z.singularBoundaryStratification.analyticFiltrationLayerNormalPair i x).relativeCohomology_isZero_of_lt n
  exact hn.trans_le (Nat.mul_le_mul_left 2
    (Z.singularBoundaryLayerChartComplement_complex_finrank_ge i x))

/-- Every neighborhood of a boundary-layer point contains an actual normal
pair with the same proved low-degree vanishing. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.exists_singularBoundaryLayerLocalPurity
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (x : (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticSpace)
    (U : Set (Z.singularBoundaryStratification.analyticFiltrationComplement i))
    (hU : U ∈ 𝓝 (Z.singularBoundaryStratification.analyticFiltrationLayerInclusion i x)) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair
        (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticModel
        (Z.singularBoundaryStratification.AnalyticFiltrationLayerChartComplement i x)
        (Z.singularBoundaryStratification.analyticFiltrationLayerInclusion i) x,
      P.ambientChart =
        (Z.singularBoundaryStratification.analyticFiltrationLayerNormalPair i x).ambientChart ∧
      P.neighborhood ⊆ U ∧
      ∀ (n : ℕ), n < 2 * (p + 1) →
        IsZero (P.relativeCohomology (ModuleCat.of ℚ ℚ) n) := by
  let := Z.singularBoundaryStratification.analyticFiltrationLayerChartComplement_finiteDimensional
    i x
  obtain ⟨P, hchart, hP⟩ :=
    Z.singularBoundaryStratification.analyticFiltrationLayerNormalPair_cofinal i x U hU
  refine ⟨P, hchart, hP, ?_⟩
  intro n hn
  apply P.relativeCohomology_isZero_of_lt n
  exact hn.trans_le (Nat.mul_le_mul_left 2
    (Z.singularBoundaryLayerChartComplement_complex_finrank_ge i x))

/-- The entire smooth layer has vanishing support cohomology below the
boundary codimension. All hypotheses of smooth support purity are supplied
by the actual algebraic layer and the proved native analytic realization. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryLayerRationalCohomology_isZero_of_lt
    (i : Fin Z.singularBoundaryStratification.analyticSupportList.length)
    (n : ℕ) (hn : n < 2 * (p + 1)) :
    IsZero (Z.singularBoundaryLayerRationalCohomology i n) := by
  let : ChartedSpace V.analyticModel (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) :=
    @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk V.structureMap)
      V.property V.presentation.smooth
  let : IsManifold 𝓘(ℂ, V.analyticModel) ω
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) :=
    @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk V.structureMap)
      V.property V.presentation.smooth ω
  let : MetrizableSpace
      (Z.singularBoundaryStratification.analyticFiltrationComplement i) :=
    Z.singularBoundaryFiltrationComplement_metrizable i
  rw [Z.singularBoundaryLayerRationalCohomology_eq_range i n]
  exact GlobalSupportPurity.Cycles.closedComplexImmersion_supportCohomology_isZero
    (E := (Z.singularBoundaryStratification.analyticFiltrationPiece i).analyticModel)
    (F := V.analyticModel)
    (Z.singularBoundaryStratification.analyticFiltrationLayerInclusion i)
    (Z.singularBoundaryStratification.isClosedEmbedding_analyticFiltrationLayerInclusion i)
    (Z.singularBoundaryStratification.contMDiff_analyticFiltrationLayerInclusion i ω)
    (Z.singularBoundaryStratification.mfderiv_analyticFiltrationLayerInclusion_injective i)
    n (Z.singularBoundaryLayer_degree_lt_realCodimension i n hn)

/-- Rational support cohomology of the genuine analytic singular boundary
vanishes below twice its proved minimal complex codimension. No purity
hypothesis for the boundary or its layers is assumed. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryRationalCohomology_isZero_of_lt
    (n : ℕ) (hn : n < 2 * (p + 1)) :
    IsZero (Z.singularBoundaryRationalCohomology n) :=
  singularBoundaryRationalCohomology_isZero_of_layers Z n
    (fun i => Z.singularBoundaryLayerRationalCohomology_isZero_of_lt i n hn)

/-- The first obstruction degree for extending a codimension-p cycle class
across its singular boundary vanishes. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryRationalCohomology_two_mul_isZero :
    IsZero (Z.singularBoundaryRationalCohomology (2 * p)) :=
  Z.singularBoundaryRationalCohomology_isZero_of_lt (2 * p) (by omega)

/-- The next obstruction degree vanishes as well, giving the two adjacent
vanishings needed for unique extension across the singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryRationalCohomology_two_mul_add_one_isZero :
    IsZero (Z.singularBoundaryRationalCohomology (2 * p + 1)) :=
  Z.singularBoundaryRationalCohomology_isZero_of_lt (2 * p + 1) (by omega)

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SingularBoundaryPurity
