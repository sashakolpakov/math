import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCoverCriterion

/-! # Unit Family Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitFamilyCoordinates

noncomputable section

/-!
# CartierDuality: the actual family coordinates of character line bundles
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} (B : Over S)

/-- The relative class of the actual line pulled back to a test-scheme family. -/
def familyLineClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (T : Over S) : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (.op T) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)

/-- The family class is natural in the actual test scheme. -/
theorem familyLineClass_natural (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) {T U : Over S} (t : U ⟶ T) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map t.op (familyLineClass B L T) = familyLineClass B L U := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ▷ B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, whiskerRight_snd]
  rfl

/-- The actual family comparison retains the class of a line pulled back from the original group. -/
theorem familyLineClass_baseChange {S' : Scheme.{u}} (s : S' ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (T : Over S') :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s T).inv
      (familyLineClass ((Over.pullback s).obj B) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (pullback.fst B.hom s) L) T) =
        familyLineClass B L ((Over.map s).obj T) := by
  have hn : (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s T).hom ≫ (snd ((Over.map s).obj T) B).left =
      (snd T ((Over.pullback s).obj B)).left ≫ pullback.fst B.hom s :=
    AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd B s T
  have he : (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s T).inv ≫
      (snd T ((Over.pullback s).obj B)).left ≫ pullback.fst B.hom s =
        (snd ((Over.map s).obj T) B).left := by
    rw [← hn, Iso.inv_hom_id_assoc]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B s T).inv
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd T ((Over.pullback s).obj B)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst B.hom s) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, Category.assoc, he]
  rfl

variable [GrpObj B]

/-- Translation of the family over the unit object is translation of the original group. -/
theorem pointShift_unitFamily_square (b : 𝟙_ (Over S) ⟶ B) :
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation B b ≫ snd (𝟙_ (Over S)) B = snd (𝟙_ (Over S)) B ≫ CharacterTranslations.Construction.KernelCharacters.pointShift b := by
  rw [Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation_snd, CharacterTranslations.Construction.KernelCharacters.pointShift_comp]
  exact congrArg (fun a => (a ≫ b) * snd (𝟙_ (Over S)) B)
    (Subsingleton.elim (fst (𝟙_ (Over S)) B) (toUnit (𝟙_ (Over S) ⊗ B)))

/-- A native translation isomorphism gives translation invariance in the genuine relative Picard sheaf. -/
theorem unitFamily_translationInvariant (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (b : 𝟙_ (Over S) ⟶ B)
    (h : Nonempty ((Scheme.Modules.pullback (CharacterTranslations.Construction.KernelCharacters.pointShift b).left).obj L.sheaf ≅ L.sheaf)) :
    Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B b (familyLineClass B L (𝟙_ (Over S))) := by
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CharacterTranslations.Construction.KernelCharacters.pointShift b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    Quotient.sound h
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (.op (𝟙_ (Over S))))
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation B b).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd (𝟙_ (Over S)) B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, pointShift_unitFamily_square, Over.comp_left,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hc]
  rfl

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitFamilyCoordinates
