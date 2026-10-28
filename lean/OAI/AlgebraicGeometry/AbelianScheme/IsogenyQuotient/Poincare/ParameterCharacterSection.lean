import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterKernelCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLineRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts

/-! # Parameter Character Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterCharacterSection.Construction

noncomputable section

section

/-! The original torsion Poincare family constructs an CartierDuality character
section, and CartierDuality's actual character line recovers that same family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (n : ℕ) [IsFinite ((𝟙 A.scheme) ^ n).left] [Flat ((𝟙 A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left]
  {Q : Over (Spec (.of k))} [IsAffine Q.left]
  (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1)

def poincareParameterCharacterSection :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))).obj.obj (.op Q) :=
  Parameter.CharacterSection.Construction.parameterCharacterSection ((𝟙 A.scheme) ^ n) Q (ParameterKernelCharacter.Construction.poincareParameterKernelCharacter D n t ht)
    (ParameterKernelCharacter.Construction.poincareParameterKernelCharacter_natural D n t ht)

theorem poincareParameterCharacterSection_value (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter ((𝟙 A.scheme) ^ n) Q (poincareParameterCharacterSection D n t ht) U z =
      ParameterKernelCharacter.Construction.poincareParameterKernelCharacter D n t ht U z :=
  Parameter.CharacterSection.Construction.parameterCharacterSection_value _ _ _ _ U z

variable [Surjective ((𝟙 A.scheme) ^ n).left]

theorem poincareParameterCharacterSection_lineClass :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine ((𝟙 A.scheme) ^ n) Q
      (poincareParameterCharacterSection D n t ht)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (TorsionParameterLine.Construction.poincareTorsionParameterLine D t) := by
  let f := (Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)
  have : IsAffineHom f.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom ((𝟙 A.scheme) ^ n)).1
  have : Flat f.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom ((𝟙 A.scheme) ^ n)).2.1
  have : Surjective f.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom ((𝟙 A.scheme) ^ n)).2.2
  have := ParameterKernelCharacter.Construction.poincareParameterKernel_projection_appTop_isIso (A := A) n Q
  have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr f
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter ((𝟙 A.scheme) ^ n) Q (poincareParameterCharacterSection D n t ht))
    (ParameterKernelCharacter.Construction.poincareParameterKernelCharacter D n t ht)
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural ((𝟙 A.scheme) ^ n) Q (poincareParameterCharacterSection D n t ht))
    (ParameterKernelCharacter.Construction.poincareParameterKernelCharacter_natural D n t ht)
    (Parameter.CharacterSection.Construction.parameterCharacterSection_recovers _ _ _ _)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f _ _) = _
  rw [he]
  exact (Quotient.sound (Kernel.CharacterLineRecovery.Construction.kernelCharacterLineRecovery f (TorsionParameterLine.Construction.poincareTorsionParameterLine D t)
    (TorsionParameterLine.Construction.poincareTorsionParameterPullbackFrame D t n ht).symm)).symm

theorem poincareParameterCharacterSection_familyClass :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass A.scheme Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine ((𝟙 A.scheme) ^ n) Q
      (poincareParameterCharacterSection D n t ht)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t) := by
  unfold CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass
  rw [poincareParameterCharacterSection_lineClass]
  exact TorsionParameterLine.Construction.poincareTorsionParameterLine_class D t

end

/-! CartierDuality's character-line map sends the constructed Poincare character
back to its original dual point on every affine parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

omit [IsAlgClosed k] in
theorem poincareTorsionFamilyLine_poincareClass {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t)) =
      Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) t := by
  have ht : lift (fst Q A.scheme ≫ t) (snd Q A.scheme) = t ▷ A.scheme := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only [lift_fst, lift_snd, whiskerRight_fst, whiskerRight_snd]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op Q)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (fst Q A.scheme ≫ t) (snd Q A.scheme)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) = _
  rw [ht]
  rfl

variable (n : ℕ) [IsFinite ((𝟙 A.scheme) ^ n).left] [Flat ((𝟙 A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left] [Surjective ((𝟙 A.scheme) ^ n).left]
  {Q : Over (Spec (.of k))} [IsAffine Q.left]
  (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1)

theorem poincareParameterCharacterSection_dualPoint :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A.scheme) ^ n) Q (poincareParameterCharacterSection D n t ht)
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) = t := by
  apply Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_injective (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) Q
  rw [CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint_poincare, poincareParameterCharacterSection_familyClass]
  exact poincareTorsionFamilyLine_poincareClass D t

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterCharacterSection.Construction
