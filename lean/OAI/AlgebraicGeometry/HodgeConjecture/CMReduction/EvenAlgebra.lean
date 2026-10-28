import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations
import OAI.AlgebraicTopology.Products.CupGradedCommutativity

/-! # Even Algebra -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAlgebra.CM.Construction

noncomputable section

/-! The actual even-degree cup products form a graded commutative semigroup.
Packing the degree together with the class makes reassociation and
reordering available without losing any of the degree transports. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CupGradedCommutativity

variable {R : Type} [CommRing R] (X : TopCat.{0})

theorem cohomologyCast_heq {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n) :
    HEq (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) h a) a := by
  subst m
  rfl

theorem cup_congr_heq {p p' q q' : ℕ} (hp : p = p') (hq : q = q')
    {a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p}
    {a' : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p'}
    {b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q}
    {b' : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q'} (ha : HEq a a') (hb : HEq b b') :
    HEq (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p q a b) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p' q' a' b') := by
  subst p'
  subst q'
  cases ha
  cases hb
  rfl

theorem evenCup_heq_cup (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p))
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (q + q)) :
    HEq (ComplexOperations.CM.Construction.evenCup R X p q a b) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X (p + p) (q + q) a b) :=
  cohomologyCast_heq (R := R) X (add_add_add_comm p p q q) _

theorem cup_assoc_heq (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X r) :
    HEq (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X (p + q) r (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p q a b) c)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p (q + r) a (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X q r b c)) :=
  (cohomologyCast_heq (R := R) X (Nat.add_assoc p q r) _).symm.trans
    (heq_of_eq (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (R := R) (p := p) (q := q) (r := r)
      (TopCat.toSSet.obj X) a b c))

theorem evenCup_assoc_heq (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p))
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (q + q))
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (r + r)) :
    HEq (ComplexOperations.CM.Construction.evenCup R X (p + q) r (ComplexOperations.CM.Construction.evenCup R X p q a b) c)
      (ComplexOperations.CM.Construction.evenCup R X p (q + r) a (ComplexOperations.CM.Construction.evenCup R X q r b c)) := by
  exact (evenCup_heq_cup (R := R) X (p + q) r _ c).trans
    ((cup_congr_heq (R := R) X
      (p := (p + q) + (p + q)) (p' := (p + p) + (q + q))
      (q := r + r) (q' := r + r) (add_add_add_comm p p q q).symm rfl
      (evenCup_heq_cup (R := R) X p q a b) (HEq.rfl)).trans
      ((cup_assoc_heq (R := R) X (p + p) (q + q) (r + r) a b c).trans
        ((cup_congr_heq (R := R) X
          (p := p + p) (p' := p + p) (q := (q + q) + (r + r))
          (q' := (q + r) + (q + r)) rfl (add_add_add_comm q q r r)
          (HEq.rfl) (evenCup_heq_cup (R := R) X q r b c).symm).trans
          (evenCup_heq_cup (R := R) X p (q + r) a _).symm)))

theorem evenCup_comm_heq (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p))
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (q + q)) :
    HEq (ComplexOperations.CM.Construction.evenCup R X p q a b) (ComplexOperations.CM.Construction.evenCup R X q p b a) := by
  have hs : (-1 : R) ^ ((p + p) * (q + q)) = 1 := by
    rw [add_mul, pow_add, ← mul_pow]
    simp
  have hc := AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm (R := R) (p := p + p) (q := q + q) X a b
  rw [hs, one_smul] at hc
  exact (evenCup_heq_cup (R := R) X p q a b).trans
    ((heq_of_eq hc).trans ((cohomologyCast_heq (R := R) X (Nat.add_comm (q + q) (p + p))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X (q + q) (p + p) b a)).trans
      (evenCup_heq_cup (R := R) X q p b a).symm))

def EvenClass := Σ p : ℕ, AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p)

theorem evenCup_one_left_heq (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p)) :
    HEq (ComplexOperations.CM.Construction.evenCup R X 0 p (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := R) X) a) a := by
  have hcast := cohomologyCast_heq (R := R) X (Nat.zero_add (p + p))
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X 0 (p + p) (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := R) X) a)
  have hunit := AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup (R := R) (p := p + p) (TopCat.toSSet.obj X) a
  have hcup : HEq
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X 0 (p + p) (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := R) X) a) a :=
    hcast.symm.trans (heq_of_eq hunit)
  exact (evenCup_heq_cup (R := R) X 0 p (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := R) X) a).trans hcup

theorem evenCup_one_right_heq (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p)) :
    HEq (ComplexOperations.CM.Construction.evenCup R X p 0 a (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := R) X)) a := by
  exact (evenCup_heq_cup (R := R) X p 0 a (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := R) X)).trans
    (heq_of_eq (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_cupUnit (R := R) (p := p + p) (TopCat.toSSet.obj X) a))

instance evenClassCommSemigroup : CommSemigroup (EvenClass (R := R) X) where
  mul a b := ⟨a.1 + b.1, ComplexOperations.CM.Construction.evenCup R X a.1 b.1 a.2 b.2⟩
  mul_assoc a b c := Sigma.ext (Nat.add_assoc a.1 b.1 c.1)
    (evenCup_assoc_heq (R := R) X a.1 b.1 c.1 a.2 b.2 c.2)
  mul_comm a b := Sigma.ext (Nat.add_comm a.1 b.1) (evenCup_comm_heq (R := R) X a.1 b.1 a.2 b.2)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAlgebra.CM.Construction
