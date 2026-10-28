import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.LineValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Normalization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction

/-! # Line Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! The normalized descended line realizes the prescribed relative
Picard map on every test scheme, by fppf separatedness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)

variable
  (q : B ⟶ Q)
  (H : ∀ {T : Over S} (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  (i : uliftYoneda.{1}.obj Q ⟶ (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj)
  (hi : ∀ (T : Over S) (a : T ⟶ B), D.relativeValue a = i.app (op T) (ULift.up (a ≫ q)))

include hi in
set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalNormalizedQuotientLine_universal_class :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op Q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.universalNormalizedQuotientLine hΓ q H)) = i.app (op Q) (ULift.up (𝟙 Q)) := by
  apply FppfSheafRestriction.Construction.fppfSheaf_restriction_injective q (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A)
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op B)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.universalNormalizedQuotientLine hΓ q H))) = _
  rw [D.universalNormalizedQuotientLine_pullback_class hΓ q H]
  have hn := (congrArg (fun t : (uliftYoneda.{1}.obj Q).obj (op Q) ⟶
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.obj (op B) => t (ULift.up (𝟙 Q))) (i.naturality q.op)).symm
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map q.op (i.app (op Q) (ULift.up (𝟙 Q))) =
    i.app (op B) (ULift.up (q ≫ 𝟙 Q)) at hn
  rw [Category.comp_id] at hn
  rw [hn, ← D.relativeValue_id]
  simpa only [Category.id_comp] using hi B (𝟙 B)

include hi in
set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalRigidifiedQuotientLine_family_value {T : Over S} (x : T ⟶ Q) :
    (D.universalRigidifiedQuotientLine hΓ q H).relativeValue x = i.app (op T) (ULift.up x) := by
  have hn := (D.universalRigidifiedQuotientLine hΓ q H).relativeValue_natural x (𝟙 Q)
  rw [Category.comp_id, Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativeValue_id] at hn
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map x.op
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.universalNormalizedQuotientLine hΓ q H))) = _ at hn
  rw [D.universalNormalizedQuotientLine_universal_class hΓ q H i hi] at hn
  have hm := (congrArg (fun t : (uliftYoneda.{1}.obj Q).obj (op Q) ⟶
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.obj (op T) => t (ULift.up (𝟙 Q))) (i.naturality x.op)).symm
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map x.op (i.app (op Q) (ULift.up (𝟙 Q))) =
    i.app (op T) (ULift.up (x ≫ 𝟙 Q)) at hm
  rw [Category.comp_id] at hm
  exact hn.symm.trans hm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
