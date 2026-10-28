import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterDualPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues

/-! # Parameterized Character Lines -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines

noncomputable section

/-!
# CartierDuality: Cartier characters parametrized by an arbitrary scheme define dual points
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- The actual scheme map identifying a family over Q with the group after base change to Q. -/
def parameterFamilyMap (B Q : Over S) : (Q ⊗ B).left ⟶ ((Over.pullback Q.hom).obj B).left :=
  ((HomogeneousCharacterLines.Construction.KernelCharacters.baseUnitIso Q).inv ▷ B).left ≫
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B Q.hom (𝟙_ (Over Q.left))).inv ≫
      (snd (𝟙_ (Over Q.left)) ((Over.pullback Q.hom).obj B)).left

/-- The actual line class on the original Q-family. -/
def parameterLineClass (B Q : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (.op Q) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (parameterFamilyMap B Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)

/-- Transport a homogeneous family class through the canonical base and unit comparisons. -/
def parameterHomogeneousClass (B Q : Over S) [GrpObj B]
    (q : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf ((Over.pullback Q.hom).obj B)).obj (.op (𝟙_ (Over Q.left)))) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).obj (.op Q) :=
  (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map (HomogeneousCharacterLines.Construction.KernelCharacters.baseUnitIso Q).inv.op
    ((Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardPresheafBaseChangeIso B Q.hom).hom.app (.op (𝟙_ (Over Q.left))) q)

/-- The homogeneous transport is exactly pullback of the actual line through the family map. -/
theorem parameterHomogeneousClass_val (B Q : Over S) [GrpObj B]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left)
    (h : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass ((Over.pullback Q.hom).obj B) (𝟙_ (Over Q.left))
      (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass ((Over.pullback Q.hom).obj B) L (𝟙_ (Over Q.left)))) :
    (parameterHomogeneousClass B Q ⟨UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass ((Over.pullback Q.hom).obj B) L _, h⟩).val =
      parameterLineClass B Q L := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((HomogeneousCharacterLines.Construction.KernelCharacters.baseUnitIso Q).inv ▷ B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B Q.hom (𝟙_ (Over Q.left))).inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd (𝟙_ (Over Q.left)) ((Over.pullback Q.hom).obj B)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, Category.assoc]
  rfl

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left] in
theorem baseChangedCover_locallyOfFinitePresentation (Q : Over S) :
    LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback Q.hom f)
    (inferInstanceAs (LocallyOfFinitePresentation f.left))

variable (Q : Over S) (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- The line over the parameter Q descended from the actual internal-Hom section. -/
def parameterCharacterLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  exact EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)

/-- The line over Q retains its actual homogeneous class. -/
def parameterCharacterHomogeneousClass : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).obj (.op Q) := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have hp : LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
    baseChangedCover_locallyOfFinitePresentation f Q
  exact parameterHomogeneousClass B Q
    (HomogeneousCharacterLines.Construction.KernelCharacters.characterHomogeneousClass ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) (𝟙_ (Over Q.left)))

theorem parameterCharacterHomogeneousClass_val :
    (parameterCharacterHomogeneousClass f Q χ).val = parameterLineClass B Q (parameterCharacterLine f Q χ) := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have hp : LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
    baseChangedCover_locallyOfFinitePresentation f Q
  exact parameterHomogeneousClass_val B Q (parameterCharacterLine f Q χ)
    (HomogeneousCharacterLines.Construction.KernelCharacters.characterDescendedLine_homogeneous ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) (𝟙_ (Over Q.left)))

/-- The actual point of the dual represented by the character line over Q. -/
def parameterCharacterDualPoint (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) : Q ⟶ D.abelian :=
  D.representable.homEquiv.symm
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (.op Q)
      (parameterCharacterHomogeneousClass f Q χ))

/-- The Poincare class is exactly the descended character line on the original family. -/
theorem parameterCharacterDualPoint_poincare (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) :
    Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (parameterCharacterDualPoint f Q χ D) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (.op Q) (parameterLineClass B Q (parameterCharacterLine f Q χ)) := by
  rw [Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation]
  have hr : D.representable.homEquiv (parameterCharacterDualPoint f Q χ D) =
      (toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (.op Q)
        (parameterCharacterHomogeneousClass f Q χ) := D.representable.homEquiv.apply_symm_apply _
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify B) (.op Q)) (parameterCharacterHomogeneousClass f Q χ)
  exact (congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (.op Q)) hr).trans
    (h.trans (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (.op Q)) (parameterCharacterHomogeneousClass_val f Q χ)))

/-- The universal Cartier character constructs an actual morphism to the Picard dual scheme. -/
def cartierToPicard (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) : C.dual.X ⟶ D.abelian :=
  parameterCharacterDualPoint f C.dual.X (C.sectionEquiv C.dual.X (𝟙 C.dual.X)) D

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines
