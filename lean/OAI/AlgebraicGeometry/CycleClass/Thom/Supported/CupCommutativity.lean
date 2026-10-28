import OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity
import OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal

/-! # Cup Commutativity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupCommutativity.Constructions

noncomputable section

/-! Even supported cups commute with the same literal target support
and degree, so geometric Thom factors can be moved to the left. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions.TwoSupportCommutativity OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem unionSwap_cohomology (X : TopCat) (A B : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (BinarySmallSwap.Constructions.unionSwap X A B) n =
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) (Set.union_comm B A)) :=
  EvenIntersectionAssociativity.Constructions.SupportedCupTargets.relativeMap_id_eqToHom X (A ∪ B) (B ∪ A) (Set.union_comm A B) n

theorem cupTo_even_comm (X : TopCat) (A B S : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (eS : A ∪ B = S) (eS' : B ∪ A = S) (p q n : ℕ) (hn : 2 * p + q = n) (hn' : q + 2 * p = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo X A B S hA hB eS (2 * p) q n hn a b =
      EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo X B A S hB hA eS' q (2 * p) n hn' b a := by
  unfold EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo SupportedCupDegrees.Constructions.cupAt
  rw [BinarySmallCupReversal.Constructions.TwoSupportCommutativity.twoSupportCup_even_comm, unionSwap_cohomology]
  simp only [← ConcreteCategory.comp_apply, eqToHom_trans]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupCommutativity.Constructions
