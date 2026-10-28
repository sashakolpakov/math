import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalThomTrace
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass

/-! # Thom Geometric Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThomGeometricCycle

noncomputable section

section

/-! The original regular Thom class has exactly the independently defined geometric trace on every compact test. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem compactCohomologyLeftCup_two_trace (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (n : ℕ) (h : 2+n = 2*d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) 2)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) h)
        (HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of M) 2 n a b)) =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d 2 n h a b := by
  rw [HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup_graded_comm]
  simp only [pow_mul, neg_one_sq, one_pow, one_smul]
  rw [HodgeConjecture.DegreeTwo.CompactCupEvaluation.Constructions.compactCohomologyDegreeCast_trans (TopCat.of M) (Nat.add_comm n 2) h (by omega)]
  exact HodgeConjecture.DegreeTwo.CompactCupTrace.Constructions.compactCohomologyRightCup_trace d n 2 (by omega) a b

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularThomClass_geometricTrace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (2 * D.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension 2 (2 * D.regularComplexDimension)
      D.regularGeometricTrace_degree
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 D.regularThomClass) b =
    D.regularGeometricTrace b := by
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2 D.regularThomClass
  have hc := compactCohomologyLeftCup_two_trace V.complexDimension (M := D.regularAmbientSpace)
    (2 * D.regularComplexDimension) (HodgeConjecture.DegreeTwo.SourceGysinTrace.Constructions.regularSourceGysinTopDegree V D)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 D.regularThomClass) b
  rw [Intrinsic.CompactThomCup.regularSourceCompactThomPushforward_cup D a ha] at hc
  exact hc.symm.trans (GlobalThomTrace.regularSourceCompactThomPushforward_trace D a ha
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension) b))

theorem regularAbsoluteThomClass_eq_geometric : D.regularAbsoluteThomClass = D.regularGeometricCycleClass := by
  apply D.regularGeometricCycleClass_unique
  intro b
  exact regularThomClass_geometricTrace D b

end

/-! The original rational divisor cycle class equals the independent geometric fundamental-trace class. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalCycleClass_eq_geometric {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) :
    D.rationalCycleClass = D.geometricCycleClass := by
  apply D.regularAmbientCohomologyRestriction_injective
  rw [D.regularAmbientCohomologyRestriction_cycleClass, D.geometricCycleClass_regularRestriction]
  exact regularAbsoluteThomClass_eq_geometric D

theorem rationalCycleClassMap_eq_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.rationalCycleClass 1 = V.geometricCycleClassMap 1 := by
  unfold Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap
  congr 1
  funext D
  exact rationalCycleClass_eq_geometric D

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThomGeometricCycle
