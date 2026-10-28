import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeProperFunctions

/-! # Parameterized Line Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterizedLineCharacters

noncomputable section

/-! Kernel-character recovery for every affine parameter family of an
abelian isogeny. The group-functions condition follows from properness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]
variable (Q : Over (Spec (.of k))) [IsAffine Q.left]

omit [IsMonHom f] in
theorem parameterKernel_groupFunctions :
    IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f))
      ((Over.pullback Q.hom).obj A)).left.appTop := by
  have hf : IsFinite ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom f inferInstance
  have hflat : Flat ((Over.pullback Q.hom).map f).left :=
    (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hfp : LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.baseChangedCover_locallyOfFinitePresentation f Q
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree ((Over.pullback Q.hom).map f) ⟨hf, hflat, hfp⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)).hom := hK.1
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)).left :=
    isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)).hom
  exact RelativeProperFunctions.Construction.properGroup_iteratedParameter_appTop_isIso A Q (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f))

def rawParameterCharacterLine
    (χ : ∀ T : Over Q.left,
      (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over Q.left} (t : U ⟶ T)
      (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)),
      Units.map t.left.appTop.hom (χ T z) = χ U (t ≫ z)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left := by
  have : IsAffineHom ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have : Flat ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have : Surjective ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  exact CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine ((Over.pullback Q.hom).map f) χ hχ

theorem parameterPullbackTrivialLine_from_kernelCharacter
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left)
    (eL : (Scheme.Modules.pullback ((Over.pullback Q.hom).map f).left).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left) :
    ∃ (χ : ∀ T : Over Q.left,
        (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(T.left, ⊤)ˣ)
      (hχ : ∀ {T U : Over Q.left} (t : U ⟶ T)
        (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)),
        Units.map t.left.appTop.hom (χ T z) = χ U (t ≫ z)),
      Nonempty (L.sheaf ≅ (rawParameterCharacterLine f Q χ hχ).sheaf) := by
  have : IsAffineHom ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have : Flat ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have : Surjective ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have : IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f))
      ((Over.pullback Q.hom).obj A)).left.appTop := parameterKernel_groupFunctions f Q
  exact RelativeCharacters.Construction.pullbackTrivialLine_from_kernelCharacter L eL

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterizedLineCharacters
