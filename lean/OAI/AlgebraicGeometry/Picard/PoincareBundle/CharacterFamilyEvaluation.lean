import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyScalars
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterCharacterValues
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations

/-! # Character Family Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyEvaluation

noncomputable section

/-! The descended character family's actual scalar evaluates the supplied internal-Hom character. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Family

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations.Construction.KernelCharacters OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterCharacterValues

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  (Q : Over S) (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- The family difference point gives the original character evaluation, on every test scheme. -/
theorem difference_value {T : Over S} (a : T ⟶ Q) (x y : T ⟶ A)
    (h : x ≫ f = y ≫ f) (q : T.left ⟶ ((Over.pullback Q.hom).obj B).left)
    (hx : (lift a x).left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q ≫ ((Over.pullback Q.hom).map f).left = q)
    (hy : (lift a y).left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q ≫ ((Over.pullback Q.hom).map f).left = q) :
    AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback Q.hom).map f) (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) q
      ((lift a x).left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) ((lift a y).left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q)
      (by rw [Category.assoc]; exact hx) (by rw [Category.assoc]; exact hy) =
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
      (χ.app (.op (Over.mk a)) (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h))).val := by
  have hpx : (ParameterCharacterValues.point a x).left ≫ ((Over.pullback Q.hom).map f).left = q := by
    rw [ParameterCharacterValues.point_left, Category.assoc]
    exact hx
  have hpy : (ParameterCharacterValues.point a y).left ≫ ((Over.pullback Q.hom).map f).left = q := by
    rw [ParameterCharacterValues.point_left, Category.assoc]
    exact hy
  have hs := AbelianScheme.CartierDuality.CharacterTranslations.Construction.KernelCharacters.differenceScalar_over ((Over.pullback Q.hom).map f) (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) q (ParameterCharacterValues.point a x) (ParameterCharacterValues.point a y) hpx hpy
  have he : ParameterCharacterValues.point a x ≫ (Over.pullback Q.hom).map f = ParameterCharacterValues.point a y ≫ (Over.pullback Q.hom).map f :=
    Over.OverMorphism.ext (hpx.trans hpy.symm)
  have hb := AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_difference Q.hom f (Over.mk a.left) (ParameterCharacterValues.point a x) (ParameterCharacterValues.point a y) he
  have hb' : AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f (Over.mk a.left)
      (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference ((Over.pullback Q.hom).map f) (ParameterCharacterValues.point a x) (ParameterCharacterValues.point a y) he) =
        (ParameterCharacterValues.testIso a).hom ≫ AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h :=
    hb.trans ((AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_congr f _ _ ((ParameterCharacterValues.testIso a).hom ≫ x) ((ParameterCharacterValues.testIso a).hom ≫ y) _
      (by rw [Category.assoc, h, Category.assoc]) (ParameterCharacterValues.point_original a x) (ParameterCharacterValues.point_original a y)).trans
        (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_natural f (ParameterCharacterValues.testIso a).hom x y h).symm)
  have hv := ParameterCharacterValues.value_eq a f χ _ (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h) hb'
  simp only [ParameterCharacterValues.point_left] at hs
  exact hs.trans (congrArg Units.val hv)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

/-- On the actual recovered family line, the canonical scalar is the supplied character value. -/
theorem scalar_value {T : Over S} (a : T ⟶ Q) (x y : T ⟶ A) (h : x ≫ f = y ≫ f)
    (q : T ⟶ Q ⊗ B) (hx : lift a x ≫ (𝟙 Q ⊗ₘ f) = q) (hy : lift a y ≫ (𝟙 Q ⊗ₘ f) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 Q ⊗ₘ f).left (CharacterFamilyLine.Family.line f Q χ).sheaf)
      (CharacterFamilyFrames.Family.pullbackFrame f Q χ) q.left (lift a x).left (lift a y).left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
      (χ.app (.op (Over.mk a)) (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f x y h))).val := by
  have hs := CharacterFamilyScalars.Family.scalar_eq f Q χ q.left (lift a x).left (lift a y).left
    (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
  exact hs.trans (difference_value f Q χ a x y h (q.left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)
    (by rw [CharacterFamilySquare.Family.square, ← Category.assoc, ← Over.comp_left, hx])
    (by rw [CharacterFamilySquare.Family.square, ← Category.assoc, ← Over.comp_left, hy]))

/-- A kernel translation recovers the original character on that precise scheme-valued kernel point. -/
theorem scalar_translation {T : Over S} (a : T ⟶ Q) (x : T ⟶ A) (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme f)
    (q : T ⟶ Q ⊗ B) (hx : lift a x ≫ (𝟙 Q ⊗ₘ f) = q)
    (hy : lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f)) ≫ (𝟙 Q ⊗ₘ f) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 Q ⊗ₘ f).left (CharacterFamilyLine.Family.line f Q χ).sheaf)
      (CharacterFamilyFrames.Family.pullbackFrame f Q χ) q.left (lift a x).left
      (lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f))).left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T (χ.app (.op (Over.mk a)) b)).val :=
  (scalar_value f Q χ a x (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f))
    (Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x b).symm q hx hy).trans
      (congrArg (fun z => (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T
        (χ.app (.op (Over.mk a)) z)).val) (AbelianScheme.CartierDuality.KernelScalarRecovery.Construction.KernelCharacters.kernelDifference_translate f x b))

end Family

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyEvaluation
