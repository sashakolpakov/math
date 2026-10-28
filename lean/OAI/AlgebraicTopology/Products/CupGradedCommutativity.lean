import OAI.AlgebraicTopology.Products.CupOppositeMap
import OAI.AlgebraicTopology.Products.CupReversalAlgebra
import OAI.AlgebraicTopology.Products.SingularReversalHomotopy

/-! # Cup Graded Commutativity -/

namespace OAI.AlgebraicTopology.Products.CupGradedCommutativity

noncomputable section

/-!
Graded commutativity of the genuine singular cohomology cup product.

Signed coordinate reversal exchanges the two blocks in the actual
Alexander--Whitney formula. Its already constructed chain homotopy to the
identity makes the induced reversal act trivially on cohomology.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {R : Type} [CommRing R]

/-- Signed reversal interchanges the two actual cochain cup factors. -/
theorem singularReversalCochainMap_cup (X : TopCat.{0}) {p q : ℕ}
    (a : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (b : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X q) :
    (SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X).f (p + q) (Cup.singularCup X a b) =
      (-1 : R) ^ (p * q) •
        Cup.cochainCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (Nat.add_comm q p)
          (Cup.singularCup X
            ((SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X).f q b)
            ((SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X).f p a)) := by
  exact CupReversalAlgebra.cup_reversal_of_evaluation X
    (fun n => ((SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X).f n).hom)
    (SingularReversalHomotopy.evaluation_singularReversalCochainMap (ModuleCat.of R R) X) a b

/-- The signed opposite-cup identity on the actual cohomology objects. -/
theorem singularReversalCochainMap_cup_cohomology (X : TopCat.{0}) {p q : ℕ}
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q) :
    HomologicalComplex.homologyMap (SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X)
        (p + q) (CupCohomology.singularCohomologyCup X p q a b) =
      (-1 : R) ^ (p * q) •
        CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (Nat.add_comm q p)
          (CupCohomology.singularCohomologyCup X q p
            (HomologicalComplex.homologyMap
              (SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X) q b)
            (HomologicalComplex.homologyMap
              (SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X) p a)) :=
  CupOppositeMap.cohomologyCup_opposite_of_cochain (TopCat.toSSet.obj X)
    (SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X) p q ((-1 : R) ^ (p * q))
    (singularReversalCochainMap_cup X) a b

/-- The genuine singular cup product is graded commutative over any
commutative coefficient ring, with equality of total degrees explicit. -/
theorem singularCohomologyCup_graded_comm (X : TopCat.{0}) {p q : ℕ}
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X q) :
    CupCohomology.singularCohomologyCup X p q a b =
      (-1 : R) ^ (p * q) •
        CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (Nat.add_comm q p)
          (CupCohomology.singularCohomologyCup X q p b a) := by
  have h := singularReversalCochainMap_cup_cohomology X a b
  simpa only [SingularReversalHomotopy.singularReversalCochainMap_homologyMap, ModuleCat.id_apply] using h

end

end OAI.AlgebraicTopology.Products.CupGradedCommutativity
