import Mathlib.Algebra.Homology.HomologicalComplex

/-! # Mono Lift -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.MonoLift

noncomputable section

/-! Componentwise factorizations through a degreewise monomorphism of
complexes assemble uniquely, with their exact factorization retained. -/

open _root_.CategoryTheory

variable {C ι : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M : HomologicalComplex C c}
  (f : K ⟶ M) (j : L ⟶ M) (hj : ∀ n, Mono (j.f n))
  (a : ∀ n, K.X n ⟶ L.X n) (ha : ∀ n, a n ≫ j.f n = f.f n)

def liftAlongMono : K ⟶ L where
  f := a
  comm' n m _ := by
    have := hj m
    apply (cancel_mono (j.f m)).mp
    rw [Category.assoc, ← j.comm n m, ← Category.assoc, ha n,
      f.comm n m, Category.assoc, ha m]

theorem liftAlongMono_factorization : liftAlongMono f j hj a ha ≫ j = f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ha n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.MonoLift
