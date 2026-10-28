import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.CompactProperCup
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass

/-! # Geometric Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace

noncomputable section

/-! The genuine regular Thom class has the independently defined geometric
fundamental trace in arbitrary codimension. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalTrace.Constructions
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.HigherThom

theorem moduleDegreeCast {F : ℕ → ModuleCat.{0} ℚ} {n m : ℕ} (h : n = m) (a : F n) :
    cast (congrArg (fun j => (F j : Type)) h) a = eqToHom (congrArg F h) a := by
  subst h
  rfl

theorem compactSupportEvaluation_degreeCast (d : ℕ) {M : Type}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] {k l n : ℕ}
    (h : k = l) (hk : k + n = 2 * d) (hl : l + n = 2 * d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) k)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d l n hl
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) h) a) b =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d k n hk a b := by
  subst h
  rfl

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularThomClass_geometricTrace_even
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (2 * D.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (2 * p) (2 * D.regularComplexDimension)
      (Normal.SourceTrace.Constructions.HigherThom.regularSourceGysinTopDegree V D)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) b =
      D.regularGeometricTrace b := by
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p) D.regularThomClass
  have hc := NormalizedLocalTrace.Constructions.compactCohomologyLeftCup_even_trace V.complexDimension p (M := D.regularAmbientSpace)
    (2 * D.regularComplexDimension) (Normal.SourceTrace.Constructions.HigherThom.regularSourceGysinTopDegree V D)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) b
  have hcup := ConcreteCategory.congr_hom
    (CompactProperCup.Constructions.HigherThom.regularSourceCompactThomPushforward_properPullback D a ha (2 * D.regularComplexDimension)) b
  change SourceCompactPushforward.Constructions.HigherThom.regularSourceCompactThomPushforward D a ha (2 * D.regularComplexDimension)
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension) b) =
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of D.regularAmbientSpace) (2 * p) (2 * D.regularComplexDimension)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) b at hcup
  rw [← hcup] at hc
  exact hc.symm.trans (GlobalTrace.Constructions.HigherThom.regularSourceCompactThomPushforward_trace D a ha
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap (2 * D.regularComplexDimension) b))

theorem regularAbsoluteThomClass_eq_cast : D.regularAbsoluteThomClass =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)) (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) (2 * p) D.regularThomClass) := by
  change cast (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of D.regularAmbientSpace) j : Type)) (two_mul p)) _ = _
  exact moduleDegreeCast (two_mul p) _

theorem regularAbsoluteThomClass_geometricTrace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (2 * D.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p) (2 * D.regularComplexDimension)
      D.regularGeometricTrace_degree D.regularAbsoluteThomClass b = D.regularGeometricTrace b := by
  rw [regularAbsoluteThomClass_eq_cast,
    compactSupportEvaluation_degreeCast V.complexDimension (two_mul p)
      (Normal.SourceTrace.Constructions.HigherThom.regularSourceGysinTopDegree V D) D.regularGeometricTrace_degree]
  exact regularThomClass_geometricTrace_even D b

theorem regularAbsoluteThomClass_eq_geometric : D.regularAbsoluteThomClass = D.regularGeometricCycleClass := by
  apply D.regularGeometricCycleClass_unique
  intro b
  exact regularAbsoluteThomClass_geometricTrace D b

theorem rationalCycleClass_eq_geometric : D.rationalCycleClass = D.geometricCycleClass := by
  apply D.regularAmbientCohomologyRestriction_injective
  rw [D.regularAmbientCohomologyRestriction_cycleClass, D.geometricCycleClass_regularRestriction]
  exact regularAbsoluteThomClass_eq_geometric D

theorem rationalCycleClassMap_eq_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    V.rationalCycleClass p = V.geometricCycleClassMap p := by
  unfold Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap
  congr 1
  funext D
  exact rationalCycleClass_eq_geometric D

end Constructions.HigherThom

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace
