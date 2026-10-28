import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterCharacterRestriction
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts

/-! # Parameter Line Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality

noncomputable section

/-!
# CartierDuality: parameterized character lines and their dual points are natural
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    {P Q : Over S} (t : P ⟶ Q)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- Restriction of the complete character datum is the complete datum of the restricted character. -/
def parameterCharacterDatum_restrictIso :
    (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor ((Over.pullback Q.hom).map f).left ((Over.pullback P.hom).map f).left
      (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t) (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square f t)).obj
      (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback Q.hom).map f)
        (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ))) ≅
    AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback P.hom).map f)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))) := by
  apply ScalarDescentSymmetry.Construction.LineDescent.nativeDatumIso_of_framedScalars ((Over.pullback P.hom).map f).left _ _
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left)) (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback P.hom).obj A).left))
  intro T q x y hx hy
  have hs := FramedBaseChange.Construction.LineDescent.framedDescentScalar_square ((Over.pullback Q.hom).map f).left
    ((Over.pullback P.hom).map f).left (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t)
    (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square f t)
    (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback Q.hom).map f)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left)) q x y hx hy
  have hq := KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) (q ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t)
    (x ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t) (y ≫ ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t)
    (by rw [Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square, ← Category.assoc, hx])
    (by rw [Category.assoc, ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square, ← Category.assoc, hy])
  have hp := KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar ((Over.pullback P.hom).map f)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
    q x y hx hy
  exact hs.trans (hq.trans ((ParameterCharacterRestriction.Construction.KernelCharacters.parameterDifferenceScalar_restrict f t χ q x y hx hy).trans hp.symm))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

/-- The actual line over a parameter scheme recovers its entire supplied native gluing. -/
def parameterCharacterLineRecoveryIso (Q : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => ((Over.pullback Q.hom).map f).left)).obj
      (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ).sheaf ≅
    AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback Q.hom).map f)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)) := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  exact OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso ((Over.pullback Q.hom).map f).left
    (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial ((Over.pullback Q.hom).obj A).left).locallyTrivial

/-- Restriction of the actual parameterized line is the line of the restricted Cartier section. -/
theorem parameterCharacterLine_restrict :
    Nonempty ((Scheme.Modules.pullback (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t)).obj (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ).sheaf ≅
      (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ)).sheaf) := by
  have ha : IsAffineHom ((Over.pullback P.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties P.hom f).1
  have hf : Flat ((Over.pullback P.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties P.hom f).2.1
  have hs : Surjective ((Over.pullback P.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties P.hom f).2.2
  exact CharacterLineBaseChange.Construction.LineDescent.recoveredLine_square_iso ((Over.pullback Q.hom).map f).left ((Over.pullback P.hom).map f).left
    (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap A t) (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_square f t)
    (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
    _ _ (parameterCharacterLineRecoveryIso f Q χ)
    (parameterCharacterLineRecoveryIso f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ))
    (parameterCharacterDatum_restrictIso f t χ)

/-- In the original family coordinates, the actual line class is natural on all parameter schemes. -/
theorem parameterCharacterLine_class_natural :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map t.op (ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
      ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B P
        (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ)) := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ)) :=
    Quotient.sound (parameterCharacterLine_restrict f t χ)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ▷ B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ))) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_natural, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h]
  rfl

variable [LocallyOfFinitePresentation f.left]

/-- The homogeneous class of the actual character line is natural before sheafification. -/
theorem parameterCharacterHomogeneousClass_natural :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map t.op (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ) =
      ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ) := by
  apply Subtype.ext
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map t.op) (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q χ)).trans
    ((parameterCharacterLine_class_natural f t χ).trans
      (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f P
        ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ)).symm)

/-- Character descent is natural in the genuine homogeneous Picard sheaf. -/
theorem parameterCharacterPicardHom_natural :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map t.op (ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ) =
      ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ) := by
  have hn := (toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).naturality_apply
    t.op (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ)
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (.op P))
    (parameterCharacterHomogeneousClass_natural f t χ))

/-- The actual character-line dual point commutes with every morphism of parameter schemes. -/
theorem parameterCharacterDualPoint_natural (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) :
    t ≫ ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D =
      ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ) D := by
  apply D.representable.homEquiv.injective
  rw [D.representable.homEquiv_comp]
  have hq : D.representable.homEquiv (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D) = ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f Q χ :=
    D.representable.homEquiv.apply_symm_apply _
  have hp : D.representable.homEquiv (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f P
      ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ) D) =
    ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f P ((CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ) :=
    D.representable.homEquiv.apply_symm_apply _
  exact (congrArg ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map t.op) hq).trans
    ((parameterCharacterPicardHom_natural f t χ).trans hp.symm)

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
