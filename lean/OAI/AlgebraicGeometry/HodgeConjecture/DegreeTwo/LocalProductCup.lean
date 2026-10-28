import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator

/-! # Local Product Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCup.Constructions

noncomputable section

/-!
# DegreeTwo: the actual local tangent–normal cup has evaluation one

The cup is the previously constructed two-support cup of the actual
projection pullbacks of the specified normal-coordinate classes. Its
evaluation is one on the actual cross of the specified homology generators.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem relativeEvaluation_changeComplement (X : TopCat.{0}) {A B : Set X}
    (h : A = B) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n)
    (z : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B n
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) h) a)
      (eqToHom (congrArg (fun S => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X S n) h) z) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A n a z := by
  subst B
  rfl

def localProductCupClass (d c : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ)))
      ({(0,0)}ᶜ) (2*d + 2*c) :=
  eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) A (2*d + 2*c))
    (RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) 0 0))
    (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) ({0}ᶜ) ({0}ᶜ)
      isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl (2*d) (2*c)
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c))

theorem localProductCupClass_evaluation (d c : ℕ) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ)))
      ({(0,0)}ᶜ) (2*d + 2*c) (localProductCupClass d c) (LocalProductGenerator.Constructions.localProductCrossGenerator d c) = 1 := by
  rw [localProductCupClass, LocalProductGenerator.Constructions.localProductCrossGenerator,
    relativeEvaluation_changeComplement _
      (RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) 0 0)]
  refine (ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation
    (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) ({0}ᶜ) ({0}ᶜ)
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl (2*d) (2*c)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c)).trans ?_
  have hd := CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_evaluation d
  have hc := CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_evaluation c
  change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) ({0}ᶜ) (2*d)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator d) = 1 at hd
  change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ)) ({0}ᶜ) (2*c)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c) = 1 at hc
  rw [hd,hc,one_mul]

theorem localProductCupClass_ne_zero (d c : ℕ) : localProductCupClass d c ≠ 0 := by
  intro h
  have he := localProductCupClass_evaluation d c
  rw [h,map_zero,LinearMap.zero_apply] at he
  exact zero_ne_one he

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCup.Constructions
