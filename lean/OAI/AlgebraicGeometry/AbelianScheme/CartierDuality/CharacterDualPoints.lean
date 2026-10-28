import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCharacterLines
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Character Dual Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterDualPoints

noncomputable section

/-!
# CartierDuality: dual points represented by actual descended character lines
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- The homogeneous classes retain the naturality of the underlying actual lines. -/
theorem characterHomogeneousClass_natural {T U : Over S} (t : U ⟶ T) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).map t.op (HomogeneousCharacterLines.Construction.KernelCharacters.characterHomogeneousClass f χ hχ T) =
      HomogeneousCharacterLines.Construction.KernelCharacters.characterHomogeneousClass f χ hχ U :=
  Subtype.ext (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass_natural B (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) t)

/-- The section of the genuine fppf Picard sheaf supplied by character descent. -/
def characterPicardSection (T : Over S) : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op T) :=
  (toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (.op T)
    (HomogeneousCharacterLines.Construction.KernelCharacters.characterHomogeneousClass f χ hχ T)

theorem characterPicardSection_natural {T U : Over S} (t : U ⟶ T) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map t.op (characterPicardSection f χ hχ T) =
      characterPicardSection f χ hχ U := by
  have hn := (toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).naturality_apply
    t.op (HomogeneousCharacterLines.Construction.KernelCharacters.characterHomogeneousClass f χ hχ T)
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (.op U))
    (characterHomogeneousClass_natural f χ hχ t))

/-- Representability sends the descended homogeneous line to an actual dual-scheme point. -/
def characterDualPoint (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (T : Over S) : T ⟶ D.abelian :=
  D.representable.homEquiv.symm (characterPicardSection f χ hχ T)

/-- The represented point is natural on every test scheme. -/
theorem characterDualPoint_natural (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) {T U : Over S} (t : U ⟶ T) :
    t ≫ characterDualPoint f χ hχ D T = characterDualPoint f χ hχ D U := by
  apply D.representable.homEquiv.injective
  rw [D.representable.homEquiv_comp]
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map t.op
    (D.representable.homEquiv (D.representable.homEquiv.symm (characterPicardSection f χ hχ T))) =
      D.representable.homEquiv (D.representable.homEquiv.symm (characterPicardSection f χ hχ U))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact characterPicardSection_natural f χ hχ t

/-- Its Poincare class is the class of the actual character line constructed by descent. -/
theorem characterDualPoint_poincare (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (T : Over S) :
    Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (characterDualPoint f χ hχ D T) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (.op T) (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) T) := by
  rw [Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation]
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (.op T)
    (D.representable.homEquiv (D.representable.homEquiv.symm (characterPicardSection f χ hχ T))) = _
  rw [Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify B) (.op T)) (HomogeneousCharacterLines.Construction.KernelCharacters.characterHomogeneousClass f χ hχ T)

omit [GrpObj A] [GrpObj B] [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    [LocallyOfFinitePresentation f.left] in
/-- Pulling a family line through a native group map is pulling the original line first. -/
theorem familyLineClass_pullback (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (T : Over S) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T) (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B L T) =
      UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f.left L) T := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T A).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

/-- The dual point lies in the actual Picard pullback kernel, detected by its canonical frame. -/
theorem characterDualPoint_pullback_trivial (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (T : Over S) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (.op T)
      (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (characterDualPoint f χ hχ D T)) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left) := by
  rw [characterDualPoint_poincare, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply,
    familyLineClass_pullback]
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T))
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ))) = _
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left := (EffectiveKernelCharacters.Construction.KernelCharacters.characterPullbackKernelClass f χ hχ).property
  rw [h, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterDualPoints
