import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterPicardInjection

/-! # Cartier Character Picard Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierCharacterPicardMap.Construction

noncomputable section

/-! The original Cartier representative maps naturally into the
actual homogeneous Picard sheaf, and its map is a monomorphism when
the original kernel has invertible exponent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

def cartierCharacterPicardSheafMap :
    uliftYoneda.{u + 1}.obj C.dual.X ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj where
  app T := TypeCat.ofHom (fun x => CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T.unop (C.sectionEquiv T.unop x.down))
  naturality {T U} a := by
    apply ConcreteCategory.ext_apply
    intro x
    change CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f U.unop (C.sectionEquiv U.unop (a.unop ≫ x.down)) = _
    rw [C.sectionEquiv_natural]
    exact (CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterPicardHom_natural f a.unop (C.sectionEquiv T.unop x.down)).symm

set_option backward.isDefEq.respectTransparency false in
theorem cartierCharacterPicardSheafMap_apply (T : Over S) (x : T ⟶ C.dual.X) :
    (cartierCharacterPicardSheafMap f C).app (op T) (ULift.up x) =
      CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T x) := by
  dsimp only [cartierCharacterPicardSheafMap]
  rfl

theorem cartierCharacterPicardSheafMap_mono
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    Mono (cartierCharacterPicardSheafMap f C) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply ConcreteCategory.mono_of_injective
  intro x y h
  apply ULift.ext
  apply (C.sectionEquiv T.unop).injective
  exact Relative.CharacterPicardInjection.Construction.parameterCharacterPicardHom_injective f C n hn hk T.unop h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierCharacterPicardMap.Construction
