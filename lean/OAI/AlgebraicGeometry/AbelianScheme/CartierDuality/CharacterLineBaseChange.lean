import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs

/-! # Character Line Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange

noncomputable section

/-!
# CartierDuality: character-line descent commutes with arbitrary scheme base change
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

namespace Construction.LineDescent

/-- An isomorphism of data in a square compares the actual recovered line bundles. -/
theorem recoveredLine_square_iso {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (s : Y' ⟶ Y) (t : X' ⟶ X) (w : t ≫ f = f' ≫ s)
    [IsAffineHom f'] [Flat f'] [Surjective f'] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y')
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (E : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f'))
    (r : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L.sheaf ≅ D)
    (r' : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f')).obj M.sheaf ≅ E)
    (b : (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f' s t w).obj D ≅ E) :
    Nonempty ((Scheme.Modules.pullback s).obj L.sheaf ≅ M.sheaf) :=
  ScalarDescentSymmetry.Construction.LineDescent.lineIso_of_ordinaryIso f' (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback s L) M
    (((Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareComparison f f' s t w).app L.sheaf).symm ≪≫
      (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f' s t w).mapIso r ≪≫ b ≪≫ r'.symm)

end Construction.LineDescent

namespace Construction.KernelCharacters

open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
    {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
/-- The original affine faithfully flat cover stays such a cover under arbitrary base change. -/
theorem baseChangedCover_properties : IsAffineHom ((Over.pullback s).map f).left ∧
    Flat ((Over.pullback s).map f).left ∧ Surjective ((Over.pullback s).map f).left :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback s f)
      (inferInstanceAs (IsAffineHom f.left)),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback s f)
      (inferInstanceAs (Flat f.left)),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback s f)
      (inferInstanceAs (Surjective f.left))⟩

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- The actual global line constructed from the base-changed character. -/
def baseChangedCharacterLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback s).obj B).left := by
  have ha : IsAffineHom ((Over.pullback s).map f).left := (baseChangedCover_properties s f).1
  have hf : Flat ((Over.pullback s).map f).left := (baseChangedCover_properties s f).2.1
  have hs : Surjective ((Over.pullback s).map f).left := (baseChangedCover_properties s f).2.2
  exact EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine ((Over.pullback s).map f) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedKernelCharacter s f χ)
    (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedKernelCharacter_natural s f χ hχ)

/-- Its complete ordinary descent recovery on the changed covering scheme. -/
def baseChangedCharacterLineRecoveryIso :
    (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => ((Over.pullback s).map f).left)).obj
      (baseChangedCharacterLine s f χ hχ).sheaf ≅
        AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedCharacterLineDatum s f χ hχ) := by
  obtain ⟨ha, hf, hs⟩ := baseChangedCover_properties s f
  exact OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso ((Over.pullback s).map f).left
    (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedCharacterLineDatum s f χ hχ) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial ((Over.pullback s).obj A).left).locallyTrivial

/-- The constructed character line commutes with arbitrary scheme base change. -/
theorem characterDescendedLine_baseChange :
    Nonempty ((Scheme.Modules.pullback (pullback.fst B.hom s)).obj (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf ≅
      (baseChangedCharacterLine s f χ hχ).sheaf) := by
  obtain ⟨ha, hf, hs⟩ := baseChangedCover_properties s f
  exact LineDescent.recoveredLine_square_iso f.left ((Over.pullback s).map f).left
    (pullback.fst B.hom s) (pullback.fst A.hom s) (KernelCharacterBaseChange.Construction.KernelCharacters.pullbackCover_square s f)
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) (baseChangedCharacterLine s f χ hχ)
    (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ))
    (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedCharacterLineDatum s f χ hχ))
    (OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso f.left (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left).locallyTrivial)
    (baseChangedCharacterLineRecoveryIso s f χ hχ) (KernelCharacterBaseChange.Construction.KernelCharacters.characterLineDatum_baseChangeIso s f χ hχ)

/-- Every lifted translation after arbitrary base change preserves the actual pulled-back line. -/
theorem characterDescendedLine_baseChange_pointShift
    (a : 𝟙_ (Over S') ⟶ (Over.pullback s).obj A) :
    Nonempty ((Scheme.Modules.pullback (CharacterTranslations.Construction.KernelCharacters.pointShift (a ≫ (Over.pullback s).map f)).left).obj
      ((Scheme.Modules.pullback (pullback.fst B.hom s)).obj (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf) ≅
        (Scheme.Modules.pullback (pullback.fst B.hom s)).obj (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf) := by
  obtain ⟨ha, hf, hs⟩ := baseChangedCover_properties s f
  obtain ⟨e⟩ := characterDescendedLine_baseChange s f χ hχ
  obtain ⟨d⟩ := CharacterTranslations.Construction.KernelCharacters.characterDescendedLine_pointShift ((Over.pullback s).map f)
    (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedKernelCharacter s f χ) (KernelCharacterBaseChange.Construction.KernelCharacters.baseChangedKernelCharacter_natural s f χ hχ) a
  exact ⟨(Scheme.Modules.pullback (CharacterTranslations.Construction.KernelCharacters.pointShift (a ≫ (Over.pullback s).map f)).left).mapIso e ≪≫ d ≪≫ e.symm⟩

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange
