import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Parameterized Character Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts

noncomputable section

/-!
# CartierDuality: character descent respects the actual Picard group law
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (Q : Over S)

/-- Evaluation of an internal-Hom product multiplies its actual regular-unit characters. -/
theorem parameterKernelCharacter_mul
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) (U : Over Q.left) :
    CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (χ * ψ) U = CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ U * CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q ψ U := by
  apply MonoidHom.ext
  intro x
  exact (CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)).map_mul
    (χ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U))) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U x))
    (ψ.app (.op (Over.mk (CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U))) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U x))

theorem parameterKernelCharacter_one (U : Over Q.left) :
    CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q 1 U = 1 := by
  apply MonoidHom.ext
  intro x
  exact (CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)).map_one

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

omit Q in
/-- Equal actual characters give equal chosen descended lines; naturality proofs do not affect the line. -/
theorem characterDescendedLine_congr
    (χ ψ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))
    (hψ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (ψ T x) = ψ U (t ≫ x)) (h : χ = ψ) :
    EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ = EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ := by
  cases h
  rfl

/-- The actual line class over each parameter scheme respects multiplication of Cartier sections. -/
theorem parameterCharacterLine_class_mul
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q (χ * ψ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q ψ) := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have he := characterDescendedLine_congr ((Over.pullback Q.hom).map f)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (χ * ψ))
    (fun U => CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ U * CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q ψ U)
    (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q (χ * ψ))
    (CharacterLineProducts.Construction.KernelCharacters.kernelCharacter_mul_natural ((Over.pullback Q.hom).map f) _ _
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q ψ))
    (funext (parameterKernelCharacter_mul f Q χ ψ))
  exact (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf he).trans
    (CharacterLineProducts.Construction.KernelCharacters.characterDescendedLine_class_mul ((Over.pullback Q.hom).map f)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)
      (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q ψ) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q ψ))

theorem parameterCharacterLine_class_one :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q 1) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj B).left := by
  have ha : IsAffineHom ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have hf : Flat ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have hs : Surjective ((Over.pullback Q.hom).map f).left := (CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have he := characterDescendedLine_congr ((Over.pullback Q.hom).map f) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q 1)
    (fun _ => 1) (CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q 1)
    (CharacterLineProducts.Construction.KernelCharacters.kernelCharacter_one_natural ((Over.pullback Q.hom).map f)) (funext (parameterKernelCharacter_one f Q))
  exact (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf he).trans
    (Quotient.sound (CharacterLineProducts.Construction.KernelCharacters.characterDescendedLine_one ((Over.pullback Q.hom).map f)))

variable [LocallyOfFinitePresentation f.left]

/-- The actual homogeneous class over Q preserves multiplication before sheafification. -/
theorem parameterCharacterHomogeneousClass_mul
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q (χ * ψ) =
      ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q χ * ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q ψ := by
  apply Subtype.ext
  have hm := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)) (parameterCharacterLine_class_mul f Q χ ψ)
  exact (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q (χ * ψ)).trans
    (hm.trans ((Picard.Homomorphisms.SchemePullback.Construction.pullbackClass_mul (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) _ _).trans
      (congrArg₂ (· * ·) (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q χ).symm
        (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q ψ).symm)))

theorem parameterCharacterHomogeneousClass_one : ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q 1 = 1 := by
  apply Subtype.ext
  exact (ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f Q 1).trans
    ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)) (parameterCharacterLine_class_one f Q)).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)))

/-- Character descent gives a homomorphism into the genuine homogeneous Picard sheaf. -/
def parameterCharacterPicardHom :
    (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q) →*
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op Q) :=
  (Picard.Homomorphisms.GroupSheafification.Construction.picardTypeSheafifyUnitHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) (.op Q)).comp
    { toFun := ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f Q
      map_one' := parameterCharacterHomogeneousClass_one f Q
      map_mul' := parameterCharacterHomogeneousClass_mul f Q }

/-- The map on dual points is a group homomorphism for the Picard-derived group law. -/
def parameterCharacterDualPointHom (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q) →* (Q ⟶ D.abelian) :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D Q).symm.toMonoidHom.comp (parameterCharacterPicardHom f Q)

/-- This homomorphism is the already constructed point represented by the actual character line. -/
theorem parameterCharacterDualPointHom_apply (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    parameterCharacterDualPointHom f Q D χ = ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f Q χ D := rfl

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts
