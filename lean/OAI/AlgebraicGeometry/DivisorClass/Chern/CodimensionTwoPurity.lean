import OAI.AlgebraicGeometry.DivisorClass.Chern.ReferencePurity
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

/-! # Codimension Two Purity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoPurity

noncomputable section

/-!
# ChernClass: removing closed subsets with no codimension-zero or one points

Two strict specialization steps force a dimension drop of at least two.
The actual finite smooth stratification then proves support cohomology
vanishing below degree four, on every analytic open.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

/-- Two strict inclusions of irreducible supports force two dimension drops. -/
theorem support_dimension_add_two_le {X : Scheme} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (Z : IrreducibleCloseds X) (hZ : 1 < Order.coheight Z) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f + 2 ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  obtain ⟨Y, W, hYW, hZY⟩ :=
    (Order.one_lt_height_iff (α := (IrreducibleCloseds X)ᵒᵈ)).mp hZ
  have h₁ := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt Z Y f hZY
  have h₂ := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt Y W f hYW
  have h₃ := Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le W f
  omega

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (F : Closeds X.carrier) (hF : ∀ z ∈ F, 1 < Order.coheight z)

/-- The actual smooth stratification of the closed subset to be removed. -/
def codimensionTwoStratification : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification X.structureMap
    (F : Set X.carrier) :=
  Classical.choice (CycleClass.Geometric.IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed X.structureMap F)

include hF in
theorem codimensionTwoPiece_dimension (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.structureMap)
    (hP : P.support ⊆ F) :
    P.dimension + 2 ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  rw [P.dimension_eq_closure]
  have hclosure : (P.closureSupport : Set X.carrier) ⊆ F := closure_minimal hP F.isClosed
  have hz : irreducibleSetEquivPoints P.closureSupport ∈ (P.closureSupport : Set X.carrier) := by
    have hm := subset_closure (Set.mem_singleton (irreducibleSetEquivPoints P.closureSupport))
    change irreducibleSetEquivPoints P.closureSupport ∈
      (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints P.closureSupport) : Set X.carrier) at hm
    simpa only [OrderIso.symm_apply_apply] using hm
  apply support_dimension_add_two_le X.structureMap P.closureSupport
  have hc := hF _ (hclosure hz)
  simpa only [Order.coheight_orderIso] using hc

include hF in
theorem codimensionTwoLayer_dimension
    (i : Fin (codimensionTwoStratification X F).analyticSupportList.length) :
    ((codimensionTwoStratification X F).analyticFiltrationPiece i).complexDimension + 2 ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  rw [CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
  apply codimensionTwoPiece_dimension X F hF
  exact (CycleClass.Geometric.IntegralSmoothStratification.support_subset_integralSmoothPiecesSupport
    ((codimensionTwoStratification X F).analyticFiltrationPiece_mem i)).trans
    (le_of_eq (codimensionTwoStratification X F).cover)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.structureMap) → ℂ

local instance : Smooth X.structureMap := X.smooth

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X.toOver ‹IsIntegral X.carrier› X.smooth

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold X.toOver ‹IsIntegral X.carrier› X.smooth ω

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) := by
  let V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨X, inferInstance⟩
  exact inferInstanceAs (MetrizableSpace V.analyticSpace)

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk X.structureMap) ‹IsIntegral X.carrier› X.smooth

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk X.structureMap) ‹IsIntegral X.carrier› X.smooth ω

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) := by
  change MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  infer_instance

include hF in
theorem codimensionTwoLayer_open_cohomology_isZero
    (i : Fin (codimensionTwoStratification X F).analyticSupportList.length)
    (U : Opens (TopCat.of ((codimensionTwoStratification X F).analyticFiltrationComplement i)))
    (n : ℕ) (hn : n < 4) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer T
        ((codimensionTwoStratification X F).analyticClosedFiltration i.castSucc)
        ((codimensionTwoStratification X F).analyticClosedFiltration i.succ)}ᶜ n) := by
  let S := codimensionTwoStratification X F
  let : MetrizableSpace (S.analyticFiltrationComplement i) := MetrizableSpace.subtype _
  have hdim : n < 2 * (Module.finrank ℂ E -
      Module.finrank ℂ (S.analyticFiltrationPiece i).analyticModel) := by
    rw [Module.finrank_fin_fun, CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank,
      ← CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
    have hd := codimensionTwoLayer_dimension X F hF i
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.structureMap] at hd
    change (S.analyticFiltrationPiece i).complexDimension + 2 ≤ _ at hd
    omega
  have h := Open.ImmersionPurity.closedComplexImmersion_open_supportCohomology_isZero
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
  have h := Open.SupportFiltration.closedSupportFiltration_open_isZero T U (ModuleCat.of ℚ ℚ)
    S.analyticSupportList.length S.analyticClosedFiltration S.analyticClosedFiltration_monotone
    S.analyticClosedFiltration_zero n
    (fun i V => codimensionTwoLayer_open_cohomology_isZero X F hF i V n hn)
  have hlast := S.analyticClosedFiltration_last
  rw [hlast] at h
  exact h

end Construction

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoPurity
