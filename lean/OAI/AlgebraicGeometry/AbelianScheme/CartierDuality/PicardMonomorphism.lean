import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Picard Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism

noncomputable section

/-!
# CartierDuality: actual character descent is a monomorphism over fields, including infinitesimal tests
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters
section

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- The actual character-line map before Picard sheafification. -/
def parameterCharacterRawMap : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj ⟶
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B where
  app T := TypeCat.ofHom (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f T.unop)
  naturality {T U} t := by
    apply ConcreteCategory.hom_ext
    intro χ
    exact (ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterHomogeneousClass_natural f t.unop χ).symm

/-- Actual character descent as a map to the homogeneous Picard sheaf. -/
def characterToPicardTypeSheafMap : CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) ⟶
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B :=
  ⟨parameterCharacterRawMap f ≫ toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)⟩

theorem characterToPicardTypeSheafMap_apply (Q : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    (characterToPicardTypeSheafMap f).hom.app (.op Q) χ = ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ := rfl

end

variable {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- Homogeneous character-line classes distinguish all Cartier sections on every affine parameter scheme. -/
theorem parameterCharacterHomogeneousClass_injective_affine (Q : Over (Spec (.of k))) [IsAffine Q.left] :
    Function.Injective (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q) := by
  have : IsIso ((Over.pullback Q.hom).obj A).hom.appTop := CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A Q
  intro χ ψ h
  apply CharacterLineFaithfulness.Construction.KernelCharacters.parameterLineClass_injective f Q
    (ConcreteCategory.bijective_of_isIso ((Over.pullback Q.hom).obj A).hom.appTop).surjective
  exact (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q χ).symm.trans
    ((congrArg Subtype.val h).trans (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q ψ))

/-- Affine cover density extends character-line detection to all parameter schemes. -/
theorem parameterCharacterHomogeneousClass_injective (Q : Over (Spec (.of k))) :
    Function.Injective (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q) := by
  intro χ ψ h
  have hd : (algSpec (.of k)).IsCoverDense (Scheme.fppfTopology.over (Spec (.of k))) :=
    SheafDescent.Construction.e56AlgSpecCoverDense (.of k)
  apply Functor.IsCoverDense.ext (algSpec (.of k)) (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) Q
  intro R t
  have : IsAffine ((algSpec (.of k)).obj R).left := by
    change IsAffine (Spec _)
    infer_instance
  apply parameterCharacterHomogeneousClass_injective_affine f ((algSpec (.of k)).obj R)
  exact (ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterHomogeneousClass_natural f t χ).symm.trans
    ((congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map t.op) h).trans
      (ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterHomogeneousClass_natural f t ψ))

/-- Sheafification retains injectivity because the character source is already an actual fppf sheaf. -/
theorem characterToPicardTypeSheafMap_injective (Q : Over (Spec (.of k))) :
    Function.Injective ((characterToPicardTypeSheafMap f).hom.app (.op Q)) := by
  let J := Scheme.fppfTopology.over (Spec (.of k))
  have hr : Presheaf.IsLocallyInjective J (parameterCharacterRawMap f) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun T => parameterCharacterHomogeneousClass_injective f T.unop)
  have hc : Sheaf.IsLocallyInjective (characterToPicardTypeSheafMap f) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J
      (parameterCharacterRawMap f ≫ toSheafify J (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)))
  exact (Sheaf.isLocallyInjective_iff_injective (characterToPicardTypeSheafMap f)).mp hc (.op Q)

theorem parameterCharacterPicardHom_injective (Q : Over (Spec (.of k))) :
    Function.Injective (ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q) :=
  characterToPicardTypeSheafMap_injective f Q

variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

omit [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] in
/-- The universal native morphism retains the represented homogeneous Picard section on every test scheme. -/
theorem cartierToPicard_representation (Q : Over (Spec (.of k))) (x : Q ⟶ C.dual.X) :
    D.representable.homEquiv (x ≫ ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) = ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q (C.sectionEquiv Q x) :=
  (congrArg D.representable.homEquiv (PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C Q x)).trans
    (D.representable.homEquiv.apply_symm_apply _)

/-- Actual character descent is a scheme-theoretic monomorphism, with all nonreduced tests retained. -/
theorem cartierToPicard_mono : Mono (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  constructor
  intro Q x y h
  apply (C.sectionEquiv Q).injective
  apply parameterCharacterPicardHom_injective f Q
  exact (cartierToPicard_representation f D C Q x).symm.trans
    ((congrArg D.representable.homEquiv h).trans (cartierToPicard_representation f D C Q y))

variable (n : ℕ) (hn : ∀ (T : Over (Spec (.of k))) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

/-- The actual morphism to dual torsion is also a scheme-theoretic monomorphism. -/
theorem cartierToPicardTorsion_mono :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    Mono (CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D n hn C) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : Mono (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := cartierToPicard_mono f D C
  constructor
  intro Q x y h
  apply (cancel_mono (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C)).mp
  rw [← CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion f D n hn C, ← Category.assoc, ← Category.assoc, h]

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardMonomorphism
