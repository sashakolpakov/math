import OAI.AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

/-! # Compact Point Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNormalization.Constructions

noncomputable section

/-! The specified point-supported dual class has actual compact trace one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem localHomologyToPoint_singleton (X : TopCat.{0}) (x : X) (n : ℕ) :
    CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X {x} x (Set.mem_singleton x) n = 𝟙 _ := by
  change CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 X) _ n = _
  exact CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_id X ({x}ᶜ : Set X) n

theorem localTranslationHomologyIso_zero (d n : ℕ) :
    (CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℂ) 0 n).hom = 𝟙 _ := by
  have he : (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ))
      (Y := TopCat.of (Fin d → ℂ)) (Homeomorph.subRight 0)).hom = 𝟙 _ := by
    ext x : 1
    exact sub_zero x
  change CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap
    (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ))
      (Y := TopCat.of (Fin d → ℂ)) (Homeomorph.subRight 0)).hom
      (by rw [he]; exact fun _ hx => hx) n = _
  simp only [he, CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_id]

theorem complexCompactSupportClass_singleton (d : ℕ) :
    CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d {0} isCompact_singleton =
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso d).inv 1 := by
  have h := CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint d {0} isCompact_singleton 0
    (Set.mem_singleton 0)
  rw [localHomologyToPoint_singleton, ModuleCat.id_apply] at h
  have hn := CycleClass.Geometric.ClosedBall.Cycles.complexCoordinatePointClass_to_origin d 0
  rw [localTranslationHomologyIso_zero, ModuleCat.id_apply] at hn
  exact h.trans hn

def compactPointDualClass (d : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
    ⟨{0}, isCompact_singleton⟩ (2*d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)

theorem compactPointDualClass_normalization (d : ℕ) :
    AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d (compactPointDualClass d) = 1 := by
  unfold compactPointDualClass
  rw [AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv_stage]
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
    ({0}ᶜ : Set (Fin d → ℂ)) (2*d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)
    (CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d {0} isCompact_singleton) = 1
  rw [complexCompactSupportClass_singleton]
  exact AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation d

theorem compactPointDualClass_ne_zero (d : ℕ) : compactPointDualClass d ≠ 0 := by
  intro h
  have hn := compactPointDualClass_normalization d
  rw [h, map_zero] at hn
  exact zero_ne_one hn

theorem compactTopClass_eq_smul_point (d : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d)) :
    a = AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d a • compactPointDualClass d := by
  apply (AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d).injective
  rw [map_smul, compactPointDualClass_normalization, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNormalization.Constructions
