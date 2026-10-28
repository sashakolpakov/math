import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitFamilyCoordinates

/-! # Homogeneous Character Lines -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCharacterLines

noncomputable section

/-!
# CartierDuality: actual kernel-character lines are homogeneous
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S : Scheme.{u}}

/-- The unit test scheme over a changed base is the original test scheme over S. -/
def baseUnitIso (T : Over S) : (Over.map T.hom).obj (𝟙_ (Over T.left)) ≅ T :=
  Over.isoMk (Iso.refl T.left) (by simp)

/-- A test-scheme point becomes a section of the actual base-changed group. -/
def pointOverOwnBase (A : Over S) [GrpObj A] (T : Over S) (a : T ⟶ A) :
    𝟙_ (Over T.left) ⟶ (Over.pullback T.hom).obj A :=
  CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv T.hom (Grp.mk A) (𝟙_ (Over T.left)) ((baseUnitIso T).hom ≫ a)

theorem pointOverOwnBase_original (A : Over S) [GrpObj A] (T : Over S) (a : T ⟶ A) :
    (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv T.hom (Grp.mk A) (𝟙_ (Over T.left))).symm
      (pointOverOwnBase A T a) = (baseUnitIso T).hom ≫ a :=
  (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv T.hom (Grp.mk A) (𝟙_ (Over T.left))).symm_apply_apply _

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

omit [IsMonHom f] in
/-- The image of that section is the original quotient point through the canonical unit comparison. -/
theorem pointOverOwnBase_image (T : Over S) (a : T ⟶ A) :
    Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B T.hom (𝟙_ (Over T.left))
      (pointOverOwnBase A T a ≫ (Over.pullback T.hom).map f) = (baseUnitIso T).hom ≫ (a ≫ f) :=
  (KernelCharacterBaseChange.Construction.KernelCharacters.pullbackPoint_symm_comp T.hom f (𝟙_ (Over T.left)) (pointOverOwnBase A T a)).trans
    ((congrArg (fun x => x ≫ f) (pointOverOwnBase_original A T a)).trans (Category.assoc _ _ _))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- Lifted translations preserve the actual relative Picard class on every test-scheme family. -/
theorem characterFamily_liftedInvariant (T : Over S) (a : T ⟶ A) :
    Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B (a ≫ f) (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) T) := by
  let Q := 𝟙_ (Over T.left)
  let A' := (Over.pullback T.hom).obj A
  let B' := (Over.pullback T.hom).obj B
  let a' : Q ⟶ A' := pointOverOwnBase A T a
  let b' : Q ⟶ B' := a' ≫ (Over.pullback T.hom).map f
  let L := EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ
  let L' := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (pullback.fst B.hom T.hom) L
  have hshift : Nonempty ((Scheme.Modules.pullback (CharacterTranslations.Construction.KernelCharacters.pointShift b').left).obj L'.sheaf ≅ L'.sheaf) :=
    CharacterLineBaseChange.Construction.KernelCharacters.characterDescendedLine_baseChange_pointShift T.hom f χ hχ a'
  have hunit : Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B' b' (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B' L' Q) :=
    UnitFamilyCoordinates.Construction.KernelCharacters.unitFamily_translationInvariant B' L' b' hshift
  have hfamily := Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant.baseChange B T.hom Q b' (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B' L' Q) hunit
  have hb : Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B T.hom Q b' = (baseUnitIso T).hom ≫ (a ≫ f) :=
    pointOverOwnBase_image f T a
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B T.hom Q).inv (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B' L' Q) =
      UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B L ((Over.map T.hom).obj Q) := UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass_baseChange B T.hom L Q
  apply Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant.of_iso B (baseUnitIso T) (a ≫ f) (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B L T)
  rw [UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass_natural]
  exact (congrArg₂ (fun b q => Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B b q) hb hc).mp hfamily

variable [LocallyOfFinitePresentation f.left]

/-- The constructed character line defines a genuine homogeneous Picard class over every test scheme. -/
theorem characterDescendedLine_homogeneous (T : Over S) :
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B T (UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) T) := by
  apply HomogeneousCoverCriterion.Construction.KernelCharacters.homogeneous_of_liftedTranslations f T
  intro U g a
  rw [UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass_natural]
  exact characterFamily_liftedInvariant f χ hχ U a

/-- The actual homogeneous class of the constructed character line, before fppf sheafification. -/
def characterHomogeneousClass (T : Over S) : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).obj (.op T) :=
  ⟨UnitFamilyCoordinates.Construction.KernelCharacters.familyLineClass B (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) T, characterDescendedLine_homogeneous f χ hχ T⟩

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCharacterLines
