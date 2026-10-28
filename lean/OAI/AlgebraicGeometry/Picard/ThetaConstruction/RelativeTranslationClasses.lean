import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Relative Translation Classes -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTranslationClasses.Geometric

noncomputable section

/-! Translation preserves equality in the original relative Picard
sheaf. The actual stabilizer of any line-bundle class is therefore a
subgroup of the original abelian family's test-scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T : Over S}

theorem translation_relativeClass_congr (a : T ⟶ A.scheme)
    (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) r) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left r) := by
  let J := Scheme.fppfTopology.over S
  let η := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme
  let F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme
  let : Presheaf.IsLocallyInjective J η :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J F))
  let R := Presheaf.equalizerSieve (F := F) (X := op T) q r
  have hR : R ∈ J T := Presheaf.equalizerSieve_mem J η q r h
  have hF := (isSheaf_iff_isSheaf_of_type J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj).mp
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).property
  apply (hF R hR).isSeparatedFor.ext
  intro U j hj
  have hq : F.map j.op (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (j ≫ a)).left (F.map j.op q) :=
    A.translationClass_naturality j a q
  have hr : F.map j.op (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left r) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (j ≫ a)).left (F.map j.op r) :=
    A.translationClass_naturality j a r
  have he := hq.trans ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (j ≫ a)).left) hj).trans hr.symm)
  exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme j _).trans
    ((congrArg (η.app (op U)) he).trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme j _).symm)

def relativeTranslationStabilizer (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    Subgroup (T ⟶ A.scheme) where
  carrier := {a | A.TranslationInvariant a q}
  one_mem' := by
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (1 : T ⟶ A.scheme)).left q) = _
    rw [A.translation_one]
    exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q)
  mul_mem' ha hb := by
    rename_i a b
    have hc : (A.translation a).left ≫ (A.translation b).left = (A.translation (a * b)).left :=
      congrArg Over.Hom.left (A.translation_comp a b)
    have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (a * b)).left q =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation b).left q) :=
      (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q) hc.symm).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp _ _ q)
    exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)) hp).trans
      ((translation_relativeClass_congr A a _ _ hb).trans ha)
  inv_mem' ha := by
    rename_i a
    have hc : (A.translation a⁻¹).left ≫ (A.translation a).left = 𝟙 (T ⊗ A.scheme).left := by
      have h := A.translation_comp a⁻¹ a
      rw [inv_mul_cancel, A.translation_one] at h
      exact congrArg Over.Hom.left h
    have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a⁻¹).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) = q :=
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp _ _ q).symm.trans
        ((congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q) hc).trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q))
    exact (translation_relativeClass_congr A a⁻¹ _ _ ha).symm.trans
      (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T)) hp)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTranslationClasses.Geometric
