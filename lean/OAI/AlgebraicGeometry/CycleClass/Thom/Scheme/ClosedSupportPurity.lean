import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.CodimensionTwoPurity
import OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology

/-! # Closed Support Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity

noncomputable section

/-! Closed algebraic support purity in every codimension on arbitrary
metrizable smooth integral finite-type complex schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

/-- The actual finite smooth stratification of the original closed set. -/
def closedSupportStratification : Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification X.hom (F : Set X.left) :=
  Classical.choice (Geometric.IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed X.hom F)

include hc in
omit [Smooth X.hom] in
theorem piece_dimension (P : Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom) (hP : P.support ⊆ F) :
    P.dimension + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  rw [P.dimension_eq_closure]
  exact hc P.closureSupport (closure_minimal hP F.isClosed)

include hc in
theorem layer_dimension (i : Fin (closedSupportStratification X F).analyticSupportList.length) :
    ((closedSupportStratification X F).analyticFiltrationPiece i).complexDimension + c ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  rw [Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
  exact piece_dimension X F c hc _
    ((closedSupportStratification X F).piece_support_subset
      ((closedSupportStratification X F).analyticFiltrationPiece_mem i))

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.hom)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk X.hom) ‹IsIntegral X.left› ‹Smooth X.hom›

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.hom)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk X.hom) ‹IsIntegral X.left› ‹Smooth X.hom› ω

variable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.hom)) := by
  change MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  infer_instance

include hc in
theorem layer_open_cohomology_isZero
    (i : Fin (closedSupportStratification X F).analyticSupportList.length)
    (U : Opens (TopCat.of ((closedSupportStratification X F).analyticFiltrationComplement i)))
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer T
        ((closedSupportStratification X F).analyticClosedFiltration i.castSucc)
        ((closedSupportStratification X F).analyticClosedFiltration i.succ)}ᶜ n) := by
  let S := closedSupportStratification X F
  let : MetrizableSpace (S.analyticFiltrationComplement i) := MetrizableSpace.subtype _
  have hdim : n < 2 * (Module.finrank ℂ E -
      Module.finrank ℂ (S.analyticFiltrationPiece i).analyticModel) := by
    rw [Module.finrank_fin_fun, Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank,
      ← Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
    have hd := layer_dimension X F c hc i
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom] at hd
    change (S.analyticFiltrationPiece i).complexDimension + c ≤ _ at hd
    omega
  have h := DivisorClass.Chern.Open.ImmersionPurity.closedComplexImmersion_open_supportCohomology_isZero
    (S.analyticFiltrationLayerInclusion i) (S.isClosedEmbedding_analyticFiltrationLayerInclusion i)
    (S.contMDiff_analyticFiltrationLayerInclusion i ω)
    (S.mfderiv_analyticFiltrationLayerInclusion_injective i) U n hdim
  simp only [S.range_analyticFiltrationLayerInclusion i] at h
  exact h

include hc in
theorem closedSupport_open_cohomology_isZero (U : Opens T) (n : ℕ) (hn : n < 2 * c) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F}ᶜ n) := by
  let S := closedSupportStratification X F
  have h := DivisorClass.Chern.Open.SupportFiltration.closedSupportFiltration_open_isZero T U (ModuleCat.of ℚ ℚ)
    S.analyticSupportList.length S.analyticClosedFiltration S.analyticClosedFiltration_monotone
    S.analyticClosedFiltration_zero n (fun i V => layer_open_cohomology_isZero X F c hc i V n hn)
  rw [S.analyticClosedFiltration_last] at h
  exact h

include hc in
theorem closedSupport_cohomology_isZero (n : ℕ) (hn : n < 2 * c) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T
      (SectionEvaluation.Constructions.analyticOpen X F.compl : Set T) n) :=
  (closedSupport_open_cohomology_isZero X F c hc ⊤ n hn).of_iso
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) T
      (SectionEvaluation.Constructions.analyticOpen X F.compl : Set T) n).symm

include hc in
/-- Actual ordinary restriction is invertible throughout the range where
both relative obstruction groups vanish. -/
theorem closedComplement_restriction_isIso (n : ℕ) (hn : n + 1 < 2 * c) :
    IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) T
      (SectionEvaluation.Constructions.analyticOpen X F.compl : Set T) n) :=
  AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology.subspaceCohomologyRestriction_isIso_of_relative_zero (ModuleCat.of ℚ ℚ) T _ n
    (closedSupport_cohomology_isZero X F c hc n (by omega))
    (closedSupport_cohomology_isZero X F c hc (n + 1) hn)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity
