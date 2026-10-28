import OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation

/-! # Codimension Two Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.CodimensionTwoPurity

noncomputable section

/-! Actual stratified purity in degrees below four on arbitrary metrizable
smooth integral complex schemes of finite type. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoPurity.Construction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left]
  (F : Closeds X.left) (hF : ∀ z ∈ F, 1 < Order.coheight z)

/-- The actual smooth stratification of the closed subset to be removed. -/
def codimensionTwoStratification : Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification X.hom
    (F : Set X.left) :=
  Classical.choice (Geometric.IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed X.hom F)

include hF in
theorem codimensionTwoPiece_dimension (P : Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom)
    (hP : P.support ⊆ F) :
    P.dimension + 2 ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  rw [P.dimension_eq_closure]
  have hclosure : (P.closureSupport : Set X.left) ⊆ F := closure_minimal hP F.isClosed
  have hz : irreducibleSetEquivPoints P.closureSupport ∈ (P.closureSupport : Set X.left) := by
    have hm := subset_closure (Set.mem_singleton (irreducibleSetEquivPoints P.closureSupport))
    change irreducibleSetEquivPoints P.closureSupport ∈
      (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints P.closureSupport) : Set X.left) at hm
    simpa only [OrderIso.symm_apply_apply] using hm
  apply DivisorClass.Chern.CodimensionTwoPurity.Construction.support_dimension_add_two_le X.hom P.closureSupport
  have hc := hF _ (hclosure hz)
  simpa only [Order.coheight_orderIso] using hc

include hF in
theorem codimensionTwoLayer_dimension
    (i : Fin (codimensionTwoStratification X F).analyticSupportList.length) :
    ((codimensionTwoStratification X F).analyticFiltrationPiece i).complexDimension + 2 ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  rw [Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
  apply codimensionTwoPiece_dimension X F hF
  exact (Geometric.IntegralSmoothStratification.support_subset_integralSmoothPiecesSupport
    ((codimensionTwoStratification X F).analyticFiltrationPiece_mem i)).trans
    (le_of_eq (codimensionTwoStratification X F).cover)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.hom)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk X.hom) ‹IsIntegral X.left› ‹Smooth X.hom›

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.hom)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk X.hom)
    ‹IsIntegral X.left› ‹Smooth X.hom› ω

variable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.hom)) := by
  change MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  infer_instance

include hF in
theorem codimensionTwoLayer_open_cohomology_isZero
    (i : Fin (codimensionTwoStratification X F).analyticSupportList.length)
    (U : Opens (TopCat.of ((codimensionTwoStratification X F).analyticFiltrationComplement i)))
    (n : ℕ) (hn : n < 4) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer T
        ((codimensionTwoStratification X F).analyticClosedFiltration i.castSucc)
        ((codimensionTwoStratification X F).analyticClosedFiltration i.succ)}ᶜ n) := by
  let S := codimensionTwoStratification X F
  let : MetrizableSpace (S.analyticFiltrationComplement i) := MetrizableSpace.subtype _
  have hdim : n < 2 * (Module.finrank ℂ E -
      Module.finrank ℂ (S.analyticFiltrationPiece i).analyticModel) := by
    rw [Module.finrank_fin_fun, Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank,
      ← Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
    have hd := codimensionTwoLayer_dimension X F hF i
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom] at hd
    change (S.analyticFiltrationPiece i).complexDimension + 2 ≤ _ at hd
    omega
  have h := DivisorClass.Chern.Open.ImmersionPurity.closedComplexImmersion_open_supportCohomology_isZero
    (S.analyticFiltrationLayerInclusion i) (S.isClosedEmbedding_analyticFiltrationLayerInclusion i)
    (S.contMDiff_analyticFiltrationLayerInclusion i ω)
    (S.mfderiv_analyticFiltrationLayerInclusion_injective i) U n hdim
  simp only [S.range_analyticFiltrationLayerInclusion i] at h
  exact h

include hF in
/-- The removed subset has no actual relative cohomology in degrees zero
through three, on any analytic open. -/
theorem codimensionTwo_open_cohomology_isZero (U : Opens T) (n : ℕ) (hn : n < 4) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F}ᶜ n) := by
  let S := codimensionTwoStratification X F
  have h := DivisorClass.Chern.Open.SupportFiltration.closedSupportFiltration_open_isZero T U (ModuleCat.of ℚ ℚ)
    S.analyticSupportList.length S.analyticClosedFiltration S.analyticClosedFiltration_monotone
    S.analyticClosedFiltration_zero n
    (fun i V => codimensionTwoLayer_open_cohomology_isZero X F hF i V n hn)
  have hlast := S.analyticClosedFiltration_last
  rw [hlast] at h
  exact h

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.CodimensionTwoPurity
