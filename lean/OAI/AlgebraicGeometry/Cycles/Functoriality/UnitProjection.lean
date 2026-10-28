import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitCap
import OAI.AlgebraicGeometry.Cycles.Functoriality.RationalCompactFundamental

/-! # Unit Projection -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.UnitProjection.Construction

noncomputable section

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings _root_.Manifold

/-- Ordinary coefficient change commutes with projection to a relative pair. -/
theorem integralToScalarHomology_relativeProjection
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (a : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A) n
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n a) =
    RationalCompactFundamental.Construction.rationalizeRelativeClass X A n
      (HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) n a) := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n a
  have hz : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A) n
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X n z) =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom n
      (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n 1
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) n z)) := by
    apply Subtype.ext
    exact (AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients.integralToRationalRelativeChainMap_projection X A n z.val).symm
  rw [AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, hz]
  apply (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).toLinearEquiv.injective
  change (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom n
        (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n 1
          (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) n z)))) =
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom ((CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv _)
  exact (AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass X A n 1
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) n z)).trans
    ((CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv_hom_id_apply _).symm

/-- The ordinary integral fundamental class projects to the canonical
compact fundamental class on every compact subset. -/
theorem complexManifoldFundamentalClass_compactProjection
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    (K : Set M) (hK : IsCompact K) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) (2 * d)
      (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d M) = CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK := by
  apply CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique d K hK
  intro x hx
  have h := congrArg (fun k => HomologicalComplex.homologyMap k (2 * d))
    (CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection (TopCat.of M) K x hx)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d M)).trans
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass_atPoint d M x)

/-- The Poincare cap of the actual cup unit is the rationalized ambient
integral fundamental class. -/
theorem poincareUnit_eq_rationalFundamental (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (V.poincareDuality (0 + 0) (2 * V.complexDimension) (by omega)).hom (UnitCap.cohomologyUnit V) =
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of V.analyticSpace) (2 * V.complexDimension)
      (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass V.complexDimension V.analyticSpace) :=
  UnitCap.Construction.mixedSingularCapHomology_unit (TopCat.of V.analyticSpace) (2 * V.complexDimension)
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass V.complexDimension V.analyticSpace)

/-- Compact projections of the unit cap are exactly the canonical
rational compact fundamental classes of the ambient manifold. -/
theorem poincareUnit_compactProjection (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (K : Set V.analyticSpace) (hK : IsCompact K) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) Kᶜ) (2 * V.complexDimension)
      ((V.poincareDuality (0 + 0) (2 * V.complexDimension) (by omega)).hom (UnitCap.cohomologyUnit V)) =
    RationalCompactFundamental.Construction.rationalCompactFundamentalClass V.complexDimension K hK := by
  rw [poincareUnit_eq_rationalFundamental, integralToScalarHomology_relativeProjection,
    complexManifoldFundamentalClass_compactProjection]
  rfl

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.UnitProjection.Construction
