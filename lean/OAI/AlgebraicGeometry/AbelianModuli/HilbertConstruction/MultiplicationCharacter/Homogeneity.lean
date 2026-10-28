import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.LineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.CharacterTranslation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.FppfPointRoots
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FamilyTranslationPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalEquality

/-! # Homogeneity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplication-character line bundles are homogeneous in the full relative Picard sense: translation invariance is proved over every test scheme by the actual fppf point-root cover. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacter_translationInvariant (T : Over (Spec (.of K))) (a : T ⟶ A.scheme)
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    A.TranslationInvariant a
      (Line.Bundles.LineBundle.classOf ((A.multiplicationCharacterLineBundle level χ hN).pullback
        (Limits.pullback.snd T.hom A.scheme.hom))) := by
  let L := A.multiplicationCharacterLineBundle level χ hN
  let LT := L.pullback (Limits.pullback.snd T.hom A.scheme.hom)
  change (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf (LT.pullback (A.translation a).left)) =
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf LT)
  obtain ⟨R, hR, hroots⟩ := A.fullLevel_fppf_pointRoots level T a
  apply Picard.LocalEquality.relativePicard_eq_of_local_bundle_iso A.scheme T (LT.pullback (A.translation a).left) LT R hR
  intro U f hf
  obtain ⟨b, hb⟩ := hroots f hf
  let LU := L.pullback (Limits.pullback.snd U.hom A.scheme.hom)
  let eb : (LU.pullback (A.translation (b ^ N)).left).sheaf ≅ LU.sheaf :=
    A.familyCharacterTranslationIso level b χ hN
  let ea : (LU.pullback (A.translation (f ≫ a)).left).sheaf ≅ LU.sheaf :=
    (Scheme.Modules.pullbackCongr
      (congrArg (fun z : U ⟶ A.scheme => (A.translation z).left) hb.symm)).app LU.sheaf ≪≫ eb
  exact ⟨Global.FamilyTranslationPullback.globalTranslatedFamilyPullbackIso A L f a ≪≫ ea ≪≫
    (Global.BundlePicardClass.globalBundleFamilyPullbackIso A.scheme L f).symm⟩

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterLineBundle_homogeneous
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    A.IsHomogeneousPicardClass (𝟙_ (Over (Spec (.of K))))
      (Line.Bundles.LineBundle.classOf ((A.multiplicationCharacterLineBundle level χ hN).pullback
        (Limits.pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom))) := by
  let L := A.multiplicationCharacterLineBundle level χ hN
  intro U f a
  have hu : (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op
      (Line.Bundles.LineBundle.classOf (L.pullback (Limits.pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom))) =
      Line.Bundles.LineBundle.classOf (L.pullback (Limits.pullback.snd U.hom A.scheme.hom)) :=
    Quotient.sound ⟨Global.BundlePicardClass.globalBundleFamilyPullbackIso A.scheme L f⟩
  have hi := A.multiplicationCharacter_translationInvariant level U a χ hN
  exact (congrArg (fun q => (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (Line.Bundles.LineBundle.pullbackClass (A.translation a).left q)) hu).trans
    (hi.trans (congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) hu.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
