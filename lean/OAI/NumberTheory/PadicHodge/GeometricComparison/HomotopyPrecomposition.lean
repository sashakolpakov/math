import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy Precomposition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition.HomotopyPrecompositionSquare

noncomputable section

/-! Precomposing a homotopy square with a commuting source square
preserves its comparison homotopy. -/

open _root_.CategoryTheory

variable {A : Type*} [Category* A] [Preadditive A]
  {K L M N P Q : CochainComplex A ℕ}
  (a : K ⟶ L) (b : M ⟶ N) (f : L ⟶ P) (g : N ⟶ Q)
  (t : P ⟶ Q) (u : K ⟶ M) (v : L ⟶ N)
  (h : Homotopy (f ≫ t) (v ≫ g)) (hs : a ≫ v = u ≫ b)

include hs in
theorem endpoint : a ≫ (v ≫ g) = u ≫ (b ≫ g) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ g) hs).trans (Category.assoc _ _ _))

def homotopy : Homotopy ((a ≫ f) ≫ t) (u ≫ (b ≫ g)) :=
  (Homotopy.ofEq (Category.assoc _ _ _)).trans
    ((h.compLeft a).trans (Homotopy.ofEq (endpoint a b g u v hs)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition.HomotopyPrecompositionSquare
