import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularBoundaryPurity
import OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Closed Support Purity -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.ClosedSupportPurity.Construction

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

/-- Actual finite smooth stratifications of arbitrary closed algebraic
subsets of the projective ambient variety. -/
def closedSupportStratification (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier) :
    CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification V.structureMap (W : Set V.carrier) := by
  let : IsNoetherian V.carrier := Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec V.structureMap
  exact Classical.choice (CycleClass.Geometric.IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed V.structureMap W)

/-- The dimensions of all irreducible closed supports bound the dimensions
of the actual smooth pieces in a closed-set stratification. -/
theorem closedSupportStratification_piece_bound
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier) (c : ℕ)
    (hc : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ W → c ≤ CycleClass.Geometric.DimensionCycles.dimensionCodimension V Z)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap)
    (hP : P ∈ (closedSupportStratification V W).pieces) :
    P.complexDimension + c ≤ V.complexDimension := by
  let : IsNoetherian V.carrier := Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec V.structureMap
  have hsub : (P.closureSupport : Set V.carrier) ⊆ W :=
    closure_minimal ((closedSupportStratification V W).piece_support_subset hP) W.isClosed
  have hcod := hc P.closureSupport hsub
  have hdim := CycleClass.Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V P.closureSupport
  rw [P.complexDimension_eq_dimension, P.dimension_eq_closure,
    V.complexDimension_eq_transcendenceDimension]
  omega

/-- Purity below the minimum complex codimension of all actual layers
extends across the whole finite algebraic stratification. -/
theorem stratified_closedSupportCohomology_isZero
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier)
    (Q : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification V.structureMap (W : Set V.carrier))
    (c : ℕ) (hc : ∀ P ∈ Q.pieces, P.complexDimension + c ≤ V.complexDimension)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set V.carrier))ᶜ n) := by
  let : ChartedSpace V.analyticModel (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) :=
    @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk V.structureMap)
      V.property V.presentation.smooth
  let : IsManifold (𝓘(ℂ, V.analyticModel)) ω
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) :=
    @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk V.structureMap)
      V.property V.presentation.smooth ω
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)) := by
    change MetrizableSpace V.analyticSpace
    infer_instance
  have hLayer (i : Fin Q.analyticSupportList.length) :
      IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Q.analyticFiltrationComplement i))
        (CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)))
          (Q.analyticClosedFiltration i.castSucc) (Q.analyticClosedFiltration i.succ))ᶜ n) := by
    let : MetrizableSpace (Q.analyticFiltrationComplement i) := by
      change MetrizableSpace
        ↥((Q.analyticClosedFiltration i.castSucc :
          Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)))ᶜ)
      infer_instance
    rw [← Q.range_analyticFiltrationLayerInclusion i]
    apply CycleClass.Geometric.GlobalSupportPurity.Cycles.closedComplexImmersion_supportCohomology_isZero
      (E := (Q.analyticFiltrationPiece i).analyticModel) (F := V.analyticModel)
      (Q.analyticFiltrationLayerInclusion i)
      (Q.isClosedEmbedding_analyticFiltrationLayerInclusion i)
      (Q.contMDiff_analyticFiltrationLayerInclusion i ω)
      (Q.mfderiv_analyticFiltrationLayerInclusion_injective i) n
    rw [V.analyticModel_complex_finrank,
      (Q.analyticFiltrationPiece i).analyticModel_complex_finrank]
    have hi := hc (Q.analyticFiltrationPiece i) (Q.analyticFiltrationPiece_mem i)
    rw [(Q.analyticFiltrationPiece i).complexDimension_eq_dimension] at hi
    omega
  have hzero := CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportFiltration_isZero (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap))) Q.analyticSupportList.length
    Q.analyticClosedFiltration Q.analyticClosedFiltration_monotone n
    (by
      simpa only [Q.analyticClosedFiltration_zero, Closeds.coe_bot] using
        CycleClass.Geometric.ClosedSupportFiltration.Cycles.cohomologyWithEmptySupport_isZero (ModuleCat.of ℚ ℚ)
          (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap))) n)
    hLayer
  change IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk V.structureMap)))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set V.carrier))ᶜ n)
  simpa only [Q.analyticClosedFiltration_last] using hzero

/-- Rational cohomology supported on an arbitrary algebraic closed set
vanishes below twice its minimum complex codimension. -/
theorem closedSupportCohomology_isZero
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier) (c : ℕ)
    (hc : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ W → c ≤ CycleClass.Geometric.DimensionCycles.dimensionCodimension V Z)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set V.carrier))ᶜ n) :=
  stratified_closedSupportCohomology_isZero V W (closedSupportStratification V W) c
    (closedSupportStratification_piece_bound V W c hc) n hn

/-- Removing an algebraic closed set of codimension greater than `p`
preserves the actual ordinary cohomology in the cycle-class degree. -/
theorem closedComplement_cohomologyRestriction_isIso
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier) (p : ℕ)
    (hc : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ W → p < CycleClass.Geometric.DimensionCycles.dimensionCodimension V Z) :
    IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set V.carrier))ᶜ (p + p)) :=
  AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology.subspaceCohomologyRestriction_isIso_of_relative_zero
    (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) _ (p + p)
    (closedSupportCohomology_isZero V W (p + 1) hc (p + p) (by omega))
    (closedSupportCohomology_isZero V W (p + 1) hc (p + p + 1) (by omega))

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.ClosedSupportPurity.Construction
