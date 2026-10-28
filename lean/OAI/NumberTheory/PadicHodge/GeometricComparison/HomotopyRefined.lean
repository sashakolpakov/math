import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy Refined -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyRefined.HomotopyRefinedSquare

noncomputable section

/-! Two comparison homotopies through a common refinement give the
original comparison square up to homotopy. -/

open _root_.CategoryTheory

variable {A : Type*} [Category* A] [Preadditive A]
  {D₂ D₁ K₂ K₁ I₂ I₁ L : CochainComplex A ℕ}
  (r₂ : D₂ ⟶ K₂) (r₁ : D₁ ⟶ K₁) (d : D₂ ⟶ D₁)
  (c₂ : K₂ ⟶ I₂) (c₁ : K₁ ⟶ I₁) (f : I₂ ⟶ I₁)
  (s₂ : K₂ ⟶ L) (s₁ : K₁ ⟶ L) (k : L ⟶ I₁)
  (h₂ : Homotopy (c₂ ≫ f) (s₂ ≫ k)) (h₁ : Homotopy c₁ (s₁ ≫ k))
  (hs : r₂ ≫ s₂ = d ≫ r₁ ≫ s₁)

def homotopy : Homotopy ((r₂ ≫ c₂) ≫ f) (d ≫ (r₁ ≫ c₁)) := by
  have h : r₂ ≫ (s₂ ≫ k) = (d ≫ r₁) ≫ (s₁ ≫ k) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ k) hs).trans
        ((congrArg (fun q => q ≫ k) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _)))
  exact (Homotopy.ofEq (Category.assoc r₂ c₂ f)).trans
    ((h₂.compLeft r₂).trans ((Homotopy.ofEq h).trans
      ((h₁.compLeft (d ≫ r₁)).symm.trans (Homotopy.ofEq (Category.assoc d r₁ c₁)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyRefined.HomotopyRefinedSquare
