import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ProductDualEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient

/-! # Product Cup Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ProductCupNormalization

noncomputable section

/-! The existing local tangent–normal cup coefficient is exactly one
for a complex line and every positive-dimensional complex tangent space. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeEvaluation_changeDegree (X : TopCat.{0}) (A : Set X) (m n : ℕ) (h : m = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A m)
    (z : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A m) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A n
      (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A) h) a)
      (eqToHom (congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A) h) z) =
      CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X A m a z := by
  subst n
  rfl

def lineTangentCupClass (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ) (2 * p + 4) :=
  eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ))
    (show 2 * 1 + 2 * (p + 1) = 2 * p + 4 by omega)) (HodgeConjecture.DegreeTwo.LocalProductCup.Constructions.localProductCupClass 1 (p + 1))

theorem lineTangentCupClass_evaluation (p : ℕ) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ) (2 * p + 4)
      (lineTangentCupClass p) (NamedLocalCrossGenerator.lineTangentCrossClass p) = 1 :=
  (relativeEvaluation_changeDegree _ _ (2 * 1 + 2 * (p + 1)) (2 * p + 4) (by omega)
    (HodgeConjecture.DegreeTwo.LocalProductCup.Constructions.localProductCupClass 1 (p + 1)) (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 (p + 1))).trans
    (HodgeConjecture.DegreeTwo.LocalProductCup.Constructions.localProductCupClass_evaluation 1 (p + 1))

def lineTangentProductCoordinates (p : ℕ) :
    ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)) ≃L[ℂ] (Fin (1 + (p + 1)) → ℂ) :=
  cast (congrArg (fun n => ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)) ≃L[ℂ] (Fin n → ℂ))
    (show p + 2 = 1 + (p + 1) by omega)) (Complex.LineProductCoordinates.complexLineProductCoordinates (p + 1))

theorem complexCoordinateLocalClass_transport_degree
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ} (h : a = b) (e : E ≃L[ℂ] (Fin a → ℂ))
    (n : ℕ) (ha : 2 * a = n) (hb : 2 * b = n) :
    eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E) hb)
      (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass (cast (congrArg (fun t => E ≃L[ℂ] (Fin t → ℂ)) h) e)) =
      eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E) ha) (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e) := by
  subst b
  rfl

theorem relativeCohomologyMap_changeDegree {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (m n : ℕ) (hm : m = n)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B m) :
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A) hm)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h m c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h n
        (eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B) hm) c) := by
  subst n
  rfl

theorem lineTangentCoordinateDualClass_eq_coordinate (p : ℕ) :
    eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)))
      (show 2 * (1 + (p + 1)) = 2 * p + 4 by omega))
      (CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass (lineTangentProductCoordinates p)) = ProductDualEvaluation.lineTangentCoordinateDualClass p := by
  refine (complexCoordinateLocalClass_transport_degree
    (show p + 2 = 1 + (p + 1) by omega) (Complex.LineProductCoordinates.complexLineProductCoordinates (p + 1))
    (2 * p + 4) (by omega) (by omega)).trans ?_
  change eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)))
    (show 2 * (p + 2) = 2 * p + 4 by omega))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (Complex.ProductFactorMaps.complexProductLineMap p) (Complex.ProductFactorMaps.complexProductLineMap_puncture p) (2 * (p + 2))
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + 2))) = _
  rw [relativeCohomologyMap_changeDegree]
  unfold ProductDualEvaluation.lineTangentCoordinateDualClass
  congr 1
  simp only [Nat.mul_succ]

theorem lineTangentCupClass_eq_coefficient_smul (p : ℕ) :
    lineTangentCupClass p = HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 1 (p + 1) • ProductDualEvaluation.lineTangentCoordinateDualClass p := by
  have h := congrArg
    (eqToHom (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)))
      (show 2 * (1 + (p + 1)) = 2 * p + 4 by omega)))
    (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop_eq_smul_coordinates 1 (p + 1) (lineTangentProductCoordinates p))
  rw [map_smul, lineTangentCoordinateDualClass_eq_coordinate] at h
  refine Eq.trans ?_ h
  unfold HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupTop lineTangentCupClass
  rw [← ConcreteCategory.comp_apply, eqToHom_trans]

theorem localProductCupCoefficient_line_positive (p : ℕ) :
    HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 1 (p + 1) = 1 := by
  have h := lineTangentCupClass_evaluation p
  rw [lineTangentCupClass_eq_coefficient_smul, map_smul] at h
  change HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient 1 (p + 1) *
    CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ) (2 * p + 4)
      (ProductDualEvaluation.lineTangentCoordinateDualClass p) (NamedLocalCrossGenerator.lineTangentCrossClass p) = 1 at h
  rw [ProductDualEvaluation.lineTangentCoordinateDualClass_evaluation, mul_one] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ProductCupNormalization
