import Mathlib.Algebra.Homology.HomologicalComplex

/-! # Monic Factor -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.MonicFactor

/-! # Factoring an actual chain map through a termwise monomorphism -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {I : Type w} {c : ComplexShape I}
  {K L M : HomologicalComplex C c}

/-- Degreewise factors form a chain map because the actual inclusion is monic in each degree. -/
def complexMonicFactor (j : L ⟶ M) (f : K ⟶ M) [∀ i, Mono (j.f i)]
    (g : ∀ i, K.X i ⟶ L.X i) (hg : ∀ i, g i ≫ j.f i = f.f i) : K ⟶ L where
  f := g
  comm' i k _ := by
    apply (cancel_mono (j.f k)).mp
    calc
      (g i ≫ L.d i k) ≫ j.f k = g i ≫ (L.d i k ≫ j.f k) := Category.assoc _ _ _
      _ = g i ≫ (j.f i ≫ M.d i k) := congrArg (g i ≫ ·) (j.comm i k).symm
      _ = (g i ≫ j.f i) ≫ M.d i k := (Category.assoc _ _ _).symm
      _ = f.f i ≫ M.d i k := congrArg (· ≫ M.d i k) (hg i)
      _ = K.d i k ≫ f.f k := f.comm i k
      _ = K.d i k ≫ (g k ≫ j.f k) := congrArg (K.d i k ≫ ·) (hg k).symm
      _ = (K.d i k ≫ g k) ≫ j.f k := (Category.assoc _ _ _).symm

theorem complexMonicFactor_comp (j : L ⟶ M) (f : K ⟶ M) [∀ i, Mono (j.f i)]
    (g : ∀ i, K.X i ⟶ L.X i) (hg : ∀ i, g i ≫ j.f i = f.f i) :
    complexMonicFactor j f g hg ≫ j = f := by
  ext i
  exact hg i

end OAI.AlgebraicGeometry.ComplexMultiplication.MonicFactor
