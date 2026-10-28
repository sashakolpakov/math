import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyOperationParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterLoci

/-! # Family Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FamilyPowers

noncomputable section

/-! Finite powers of a pointed projective family are actual projective parameters for finite ordered tuples of family points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} (A : Over S)

def finiteFamilyPower : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | n + 1 => A ⊗ finiteFamilyPower n

def finiteFamilyPowerPoints (n : ℕ) (T : Over S) : (T ⟶ FamilyPowers.finiteFamilyPower A n) ≃ (Fin n → (T ⟶ A)) := by
  induction n with
  | zero =>
      exact
        { toFun := fun _ i => Fin.elim0 i
          invFun := fun _ => toUnit T
          left_inv := fun _ => toUnit_unique _ _
          right_inv := fun _ => funext (fun i => Fin.elim0 i) }
  | succ n ih =>
      refine ((Bounded.FamilyOperationParameters.overTensorPointEquiv A (FamilyPowers.finiteFamilyPower A n) T).trans
        (Equiv.prodCongr (Equiv.refl _) ih)).trans ?_
      exact
        { toFun := fun p => Fin.cases p.1 p.2
          invFun := fun p => (p 0, fun i => p i.succ)
          left_inv := fun _ => rfl
          right_inv := fun p => funext (fun i => Fin.cases rfl (fun _ => rfl) i) }

theorem finiteFamilyPowerPoints_natural (n : ℕ) {U T : Over S} (c : U ⟶ T)
    (p : T ⟶ FamilyPowers.finiteFamilyPower A n) (i : Fin n) :
    finiteFamilyPowerPoints A n U (c ≫ p) i = c ≫ finiteFamilyPowerPoints A n T p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change (c ≫ p) ≫ fst A (FamilyPowers.finiteFamilyPower A n) = c ≫ (p ≫ fst A (FamilyPowers.finiteFamilyPower A n))
        exact Category.assoc c p (fst A (FamilyPowers.finiteFamilyPower A n))
      · change finiteFamilyPowerPoints A n U ((c ≫ p) ≫ snd A (FamilyPowers.finiteFamilyPower A n)) j =
          c ≫ finiteFamilyPowerPoints A n T (p ≫ snd A (FamilyPowers.finiteFamilyPower A n)) j
        exact (congrArg (fun q : U ⟶ FamilyPowers.finiteFamilyPower A n => finiteFamilyPowerPoints A n U q j)
          (Category.assoc c p (snd A (FamilyPowers.finiteFamilyPower A n)))).trans
            (ih (p ≫ snd A (FamilyPowers.finiteFamilyPower A n)) j)

def finiteFamilyPowerProjective (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (x : 𝟙_ (Over S) ⟶ A) [hx : IsClosedImmersion x.left] :
    (n : ℕ) → Projective.ProjectivePresentations.ProjectivePresentation (FamilyPowers.finiteFamilyPower A n)
  | 0 => @Projective.ProjectivePresentations.ProjectivePresentation.ofClosedImmersion S A (𝟙_ (Over S)) P x hx
  | n + 1 => P.product (finiteFamilyPowerProjective P x n)

def finiteLabelFamilyPower (I : Type u) [Fintype I] : Over S := FamilyPowers.finiteFamilyPower A (Fintype.card I)

def finiteLabelFamilyPowerPoints (I : Type u) [Fintype I] (T : Over S) :
    (T ⟶ finiteLabelFamilyPower A I) ≃ (I → (T ⟶ A)) :=
  (finiteFamilyPowerPoints A (Fintype.card I) T).trans
    (Equiv.arrowCongr (Fintype.equivFin I).symm (Equiv.refl _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FamilyPowers
