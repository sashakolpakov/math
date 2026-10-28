import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality

/-! # Equivalent Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EquivalentPresheafSections

noncomputable section

/-!
# IntegralComparison: restriction along an actual site equivalence identifies presheaf sections naturally
-/

open _root_.CategoryTheory

universe u v w z t

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {A : Type w} [Category.{z} A] [Preadditive A]
  (R : Type t) [CommRing R] [Linear R A] (E : D ⥤ C) [E.IsEquivalence] (M : A)

def map (P : Cᵒᵖ ⥤ A) : ((Functor.const Cᵒᵖ).obj M ⟶ P) →ₗ[R]
    ((Functor.const Dᵒᵖ).obj M ⟶ E.op ⋙ P) where
  toFun a := Functor.whiskerLeft E.op a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bijective (P : Cᵒᵖ ⥤ A) : Function.Bijective (map R E M P) := by
  let W := (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj E.op
  exact ⟨W.map_injective, W.map_surjective⟩

def linearEquiv (P : Cᵒᵖ ⥤ A) : ((Functor.const Cᵒᵖ).obj M ⟶ P) ≃ₗ[R]
    ((Functor.const Dᵒᵖ).obj M ⟶ E.op ⋙ P) := LinearEquiv.ofBijective (map R E M P) (bijective R E M P)

theorem naturality {P Q : Cᵒᵖ ⥤ A} (a : (Functor.const Cᵒᵖ).obj M ⟶ P) (b : P ⟶ Q) :
    linearEquiv R E M Q (a ≫ b) = linearEquiv R E M P a ≫ Functor.whiskerLeft E.op b := rfl

def iso : ExhaustiveSectionNaturality.globalSectionsFunctor (C := C) R M ≅
    (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj E.op ⋙
      ExhaustiveSectionNaturality.globalSectionsFunctor (C := D) R M :=
  NatIso.ofComponents (fun P => (linearEquiv R E M P).toModuleIso) (by
    intro P Q b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact naturality R E M a b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EquivalentPresheafSections
