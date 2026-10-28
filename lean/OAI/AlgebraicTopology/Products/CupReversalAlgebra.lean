import OAI.AlgebraicTopology.Products.Cup
import OAI.AlgebraicTopology.Products.ReversalSigns
import OAI.AlgebraicTopology.Products.SimplexReversal

/-! # Cup Reversal Algebra -/

namespace OAI.AlgebraicTopology.Products.CupReversalAlgebra

/-!
The algebraic effect of genuine signed simplex reversal on the
Alexander--Whitney cup formula. The evaluation hypothesis specifies the
degreewise action completely; it is instantiated by the actual dual chain map.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {R : Type} [CommRing R]

/-- A degreewise action with the actual signed-reversal evaluations interchanges
the two cup factors with the Koszul sign. No cochain homotopy is needed here. -/
theorem cup_reversal_of_evaluation (X : TopCat.{0})
    (f : ∀ n, (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X n →ₗ[R]
      (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X n)
    (hf : ∀ n (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X n)
      (s : (TopCat.toSSet.obj X) _⦋n⦌),
      Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of R R) s (f n c) =
        ReversalSigns.reversalSign n • Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of R R)
          (SimplexReversal.singularSimplexReversal X n s) c)
    {p q : ℕ} (a : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (b : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X q) :
    f (p + q) (Cup.singularCup X a b) =
      (-1 : R) ^ (p * q) •
        Cup.cochainCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (Nat.add_comm q p)
          (Cup.singularCup X (f q b) (f p a)) := by
  apply Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of R R)
  intro s
  have hleft := Cup.evaluation_cup (TopCat.toSSet.obj X) a b
    (SimplexReversal.singularSimplexReversal X (p + q) s)
  rw [SimplexReversal.frontFace_singularSimplexReversal, SimplexReversal.backFace_singularSimplexReversal] at hleft
  have hcast := Cup.evaluation_cochainCast (TopCat.toSSet.obj X) (ModuleCat.of R R)
    (Nat.add_comm q p) (Cup.singularCup X (f q b) (f p a)) s
  have hright := Cup.evaluation_cup (TopCat.toSSet.obj X) (f q b) (f p a)
    (SimplexFaceIdentities.simplexCast (TopCat.toSSet.obj X) (Nat.add_comm q p).symm s)
  rw [hf, hf] at hright
  rw [hf, map_smul, hcast, hright, hleft]
  simp only [zsmul_eq_mul, smul_eq_mul]
  rw [ReversalSigns.reversalSign_cast_add]
  ring

end OAI.AlgebraicTopology.Products.CupReversalAlgebra
