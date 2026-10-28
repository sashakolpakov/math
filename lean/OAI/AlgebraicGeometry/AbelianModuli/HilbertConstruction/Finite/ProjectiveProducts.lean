import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Projective Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Nonempty finite products preserve actual projective presentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

def Finite.ProjectiveProducts.overFinOneProductIso (F : Fin 1 → Over S) : (∏ᶜ F) ≅ F 0 where
  hom := Pi.π F 0
  inv := Pi.lift (fun i => eqToHom (congrArg F (Subsingleton.elim 0 i)))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  inv_hom_id := by simp

def Projective.ProjectivePresentations.ProjectivePresentation.binaryProduct {X Y : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y) :
    Projective.ProjectivePresentations.ProjectivePresentation (X ⨯ Y) :=
  (P.product Q).ofSourceIso ((CartesianMonoidalCategory.tensorLeftIsoProd X).app Y).symm

def Finite.ProjectiveProducts.overNonemptyFinProductPresentation (n : ℕ) (F : Fin (n + 1) → Over S)
    (P : ∀ i, Projective.ProjectivePresentations.ProjectivePresentation (F i)) : Projective.ProjectivePresentations.ProjectivePresentation (∏ᶜ F) := by
  induction n with
  | zero => exact (P 0).ofSourceIso (Finite.ProjectiveProducts.overFinOneProductIso F)
  | succ n ih =>
      let Q := ih (fun i => F i.succ) (fun i => P i.succ)
      exact ((P 0).binaryProduct Q).ofSourceIso (Finite.ProperProducts.overFinProductSuccIso F)

def Finite.ProjectiveProducts.overFinProductPresentation (n : ℕ) [Nonempty (Fin n)] (F : Fin n → Over S)
    (P : ∀ i, Projective.ProjectivePresentations.ProjectivePresentation (F i)) : Projective.ProjectivePresentations.ProjectivePresentation (∏ᶜ F) := by
  cases n with
  | zero => exact False.elim (Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0))))
  | succ n => exact Finite.ProjectiveProducts.overNonemptyFinProductPresentation n F P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
