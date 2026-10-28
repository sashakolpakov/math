import OAI.AlgebraicGeometry.Cycles.Functoriality.ClosedSupportPurity
import OAI.AlgebraicTopology.Duality.Poincare.CompactTraceEvaluation
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd

/-! # Trace Detection -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.TraceDetection.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

/-- Compact relative traces in an open subset detect ordinary homology
whenever the corresponding cohomology restriction is injective. -/
theorem ordinaryHomology_eq_of_openCompactTraces
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    (U : Opens M) (p q : ℕ) (hpq : p + q = 2 * d) (hp : Even p)
    (hinj : Function.Injective (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p))
    (a b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q)
    (htrace : ∀ K : Compacts U,
      AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace (X := TopCat.of M) U K q a =
      AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace (X := TopCat.of M) U K q b) : a = b := by
  let e := AlgebraicTopology.Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality d (M := M) p q hpq
  have ha : AlgebraicTopology.Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq (e.inv a) = a :=
    e.inv_hom_id_apply a
  have hb : AlgebraicTopology.Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq (e.inv b) = b :=
    e.inv_hom_id_apply b
  apply e.symm.toLinearEquiv.injective
  change e.inv a = e.inv b
  apply hinj
  apply (AlgebraicTopology.Duality.Poincare.CompactSupportAnd.cohomology_eq_iff_compactSupportEvaluation_eq d (M := U) p q hpq _ _).mpr
  intro t
  obtain ⟨K, c, rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
    (TopCat.of U) q t
  rw [← AlgebraicTopology.Duality.Poincare.CompactTraceEvaluation.complexManifoldOrdinaryCap_openCompactRelativeTrace_evaluation d U K p q hpq hp,
    ← AlgebraicTopology.Duality.Poincare.CompactTraceEvaluation.complexManifoldOrdinaryCap_openCompactRelativeTrace_evaluation d U K p q hpq hp,
    ha, hb, htrace K]

/-- The genuine analytic open complement of an algebraic closed set. -/
def algebraicComplementOpen (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (W : Closeds V.carrier) : Opens V.analyticSpace :=
  ⟨(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set V.carrier))ᶜ,
    (W.isClosed.preimage ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying).isOpen_compl⟩

/-- Classes in the complementary homology degree are detected by all
compact traces outside any algebraic set of sufficiently large codimension. -/
theorem ordinaryHomology_eq_of_traces_outside_closed
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier) (p q : ℕ)
    (hpq : (p + p) + q = 2 * V.complexDimension)
    (hc : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ W → p < CycleClass.Geometric.DimensionCycles.dimensionCodimension V Z)
    (a b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology q)
    (htrace : ∀ K : Compacts (algebraicComplementOpen V W),
      AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace (X := TopCat.of V.analyticSpace) (algebraicComplementOpen V W) K q a =
      AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace (X := TopCat.of V.analyticSpace) (algebraicComplementOpen V W) K q b) :
    a = b := by
  apply ordinaryHomology_eq_of_openCompactTraces V.complexDimension (algebraicComplementOpen V W)
    (p + p) q hpq ⟨p, rfl⟩ _ a b htrace
  let r := AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set V.carrier))ᶜ (p + p)
  let : IsIso r := ClosedSupportPurity.Construction.closedComplement_cohomologyRestriction_isIso V W p hc
  exact (ConcreteCategory.bijective_of_isIso r).1

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.TraceDetection.Construction
