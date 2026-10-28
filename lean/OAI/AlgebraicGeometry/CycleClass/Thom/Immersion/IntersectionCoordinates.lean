import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalDimension

/-! # Intersection Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

noncomputable section

/-! Simultaneous charts for closed complex immersions, constructed from
the surjective differential of their canonical normal equations. -/

open scoped ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions
  Intersection.NormalPair.Constructions Intersection.NormalDimension.Constructions

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ}
  (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (W : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V q)

def NormalTransverse : Prop :=
  ∀ (x : Z.regularAnalyticSpace) (y : W.regularAnalyticSpace),
    Z.regularComplementInclusion x = W.regularComplementInclusion y →
    Function.Surjective (fderiv ℂ
      (Intersection.NormalPair.Constructions.intersectionEquations (Z.regularFixedNormalPair x) (W.regularFixedNormalPair y)
        (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates p q)) 0)

theorem regularFixedNormalPair_contMDiff (x : Z.regularAnalyticSpace) :
    ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ω
      (Z.regularFixedNormalPair x).ambientChart (Z.regularFixedNormalPair x).ambientChart.source :=
  ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates (Z.regularFixedComplementImmersion x)

theorem regularFixedNormalPair_symm_contMDiff (x : Z.regularAnalyticSpace) :
    ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) 𝓘(ℂ, V.analyticModel) ω
      (Z.regularFixedNormalPair x).ambientChart.symm (Z.regularFixedNormalPair x).ambientChart.target :=
  ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates_symm (Z.regularFixedComplementImmersion x)

theorem exists_intersection_normalPair (S : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V (p + q))
    (hw : Set.range S.regularComplementInclusion =
      Set.range Z.regularComplementInclusion ∩ Set.range W.regularComplementInclusion)
    (ht : NormalTransverse Z W) (z : S.regularAnalyticSpace) :
    ∃ (x : Z.regularAnalyticSpace) (y : W.regularAnalyticSpace)
      (R : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair S.regularAnalyticModel (Fin (p + q) → ℂ)
        S.regularComplementInclusion z),
      R.neighborhood ⊆ (Z.regularFixedNormalPair x).neighborhood ∩
        (W.regularFixedNormalPair y).neighborhood ∧
      R.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
        𝓘(ℂ, S.regularAnalyticModel × (Fin (p + q) → ℂ)) ∧
      ∀ a : R.neighborhood, R.normalCoordinate a = HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates p q
        (((Z.regularFixedNormalPair x).ambientChart a.val).2,
          ((W.regularFixedNormalPair y).ambientChart a.val).2) := by
  have hz : S.regularComplementInclusion z ∈ Set.range Z.regularComplementInclusion ∩
      Set.range W.regularComplementInclusion := hw ▸ Set.mem_range_self z
  obtain ⟨x, hx⟩ := hz.1
  obtain ⟨y, hy⟩ := hz.2
  refine ⟨x, y, ?_⟩
  apply Intersection.NormalDimension.Constructions.exists_intersection_normalPair_of_dimension
    (Z.regularFixedNormalPair x) (W.regularFixedNormalPair y) (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates p q)
    S.regularComplementInclusion z (hx.trans hy.symm) hx hw
    (Z.regularFixedNormalPair_ambientChart_mdifferentiable x)
    (regularFixedNormalPair_symm_contMDiff Z x) (regularFixedNormalPair_contMDiff W y)
    (ht x y (hx.trans hy.symm))
  simpa only [Closed.ComplexImmersion.Constructions.ClosedComplexImmersion.regularAnalyticModel, Closed.ComplexImmersion.Constructions.ComplexManifold.analyticModel, Module.finrank_fin_fun]
    using S.regularComplexDimension_add_codimension

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions
