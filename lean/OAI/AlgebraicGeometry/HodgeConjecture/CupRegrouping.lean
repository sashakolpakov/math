import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
import OAI.AlgebraicTopology.Products.CupGradedCommutativity

/-! # Cup Regrouping -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CupRegrouping.CM.SurfaceConstruction

noncomputable section

/-! The actual Koszul regrouping of four divisor pairs. All products below
are the descended singular Alexander--Whitney cup product. -/

open _root_.CategoryTheory

variable {R : Type} [CommRing R] (X : TopCat.{0})

private abbrev H (n : ℕ) := AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n
private abbrev cup (p q : ℕ) := AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p q

private theorem assoc111 (a b c : H (R := R) X 1) :
    cup X 2 1 (cup X 1 1 a b) c = cup X 1 2 a (cup X 1 1 b c) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (TopCat.toSSet.obj X) a b c

private theorem assoc112 (a b : H (R := R) X 1) (c : H (R := R) X 2) :
    cup X 2 2 (cup X 1 1 a b) c = cup X 1 3 a (cup X 1 2 b c) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (TopCat.toSSet.obj X) a b c

private theorem assoc222 (a b c : H (R := R) X 2) :
    cup X 4 2 (cup X 2 2 a b) c = cup X 2 4 a (cup X 2 2 b c) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (TopCat.toSSet.obj X) a b c

private theorem assoc224 (a b : H (R := R) X 2) (c : H (R := R) X 4) :
    cup X 4 4 (cup X 2 2 a b) c = cup X 2 6 a (cup X 2 4 b c) :=
  AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_assoc (TopCat.toSSet.obj X) a b c

theorem cup11_anticomm (a b : H (R := R) X 1) :
    cup X 1 1 a b = -cup X 1 1 b a := by
  simpa only [Nat.one_mul, pow_one, AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply, neg_one_smul] using
    AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm X a b

theorem cup22_comm (a b : H (R := R) X 2) :
    cup X 2 2 a b = cup X 2 2 b a := by
  simpa only [show (-1 : R) ^ (2 * 2) = 1 by ring,
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply, one_smul] using AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm X a b

theorem cup44_comm (a b : H (R := R) X 4) :
    cup X 4 4 a b = cup X 4 4 b a := by
  simpa only [show (-1 : R) ^ (4 * 4) = 1 by ring,
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply, one_smul] using AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm X a b

theorem cup12_comm (a : H (R := R) X 1) (b : H (R := R) X 2) :
    cup X 1 2 a b = cup X 2 1 b a := by
  simpa only [show (-1 : R) ^ (1 * 2) = 1 by ring,
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply, one_smul] using AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm X a b

theorem cup1111_cycle (a b c d : H (R := R) X 1) :
    cup X 2 2 (cup X 1 1 a b) (cup X 1 1 c d) =
      cup X 2 2 (cup X 1 1 a c) (cup X 1 1 d b) := by
  rw [assoc112, cup12_comm, assoc111, ← assoc112]

theorem cup1111_cycle_twice (a b c d : H (R := R) X 1) :
    cup X 2 2 (cup X 1 1 a b) (cup X 1 1 c d) =
      cup X 2 2 (cup X 1 1 a d) (cup X 1 1 b c) :=
  (cup1111_cycle X a b c d).trans (cup1111_cycle X a c d b)

theorem cup1111_exchange (a b c d : H (R := R) X 1) :
    cup X 2 2 (cup X 1 1 a b) (cup X 1 1 c d) =
      -cup X 2 2 (cup X 1 1 a c) (cup X 1 1 b d) := by
  rw [assoc112, ← assoc111, cup11_anticomm X b c]
  simp only [map_neg, LinearMap.neg_apply]
  rw [assoc111, ← assoc112]

theorem cup2222_exchange (a b c d : H (R := R) X 2) :
    cup X 4 4 (cup X 2 2 a b) (cup X 2 2 c d) =
      cup X 4 4 (cup X 2 2 a c) (cup X 2 2 b d) := by
  rw [assoc224, ← assoc222, cup22_comm X b c, assoc222, ← assoc224]

/-- Moving the four second coordinates past the first coordinates gives
six odd-degree transpositions, hence the positive sign in the actual cup. -/
theorem four_pair_cup_regroup (a b : Fin 4 → H (R := R) X 1) :
    cup X 4 4
        (cup X 2 2 (cup X 1 1 (a 0) (b 0)) (cup X 1 1 (a 1) (b 1)))
        (cup X 2 2 (cup X 1 1 (a 2) (b 2)) (cup X 1 1 (a 3) (b 3))) =
      cup X 4 4
        (cup X 2 2 (cup X 1 1 (a 0) (a 1)) (cup X 1 1 (a 2) (a 3)))
        (cup X 2 2 (cup X 1 1 (b 0) (b 1)) (cup X 1 1 (b 2) (b 3))) := by
  rw [cup1111_exchange X (a 0) (b 0) (a 1) (b 1),
    cup1111_exchange X (a 2) (b 2) (a 3) (b 3)]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact cup2222_exchange X _ _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CupRegrouping.CM.SurfaceConstruction
