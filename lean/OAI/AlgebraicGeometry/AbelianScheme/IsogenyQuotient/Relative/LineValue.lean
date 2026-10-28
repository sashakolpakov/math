import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Normalization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction

/-! # Line Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

/-! The normalized descended line realizes the prescribed relative
Picard map on every test scheme, by fppf separatedness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativeValue_id : D.relativeValue (𝟙 B) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op B) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) := by
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op B)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 B) ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)) = _
  rw [tensorHom_id, id_whiskerRight, Over.id_left]
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op B)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle))

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  (q : B ⟶ Q)
  (H : ∀ {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B),
    a ≫ q = b ≫ q → D.relativeValue a = D.relativeValue b)
  [IsAffineHom (q ⊗ₘ 𝟙 A).left] [Flat (q ⊗ₘ 𝟙 A).left]
  [Surjective (q ⊗ₘ 𝟙 A).left] [LocallyOfFinitePresentation (q ⊗ₘ 𝟙 A).left]
  [IsLocallyNoetherian (Q ⊗ A).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
  (i : uliftYoneda.{1}.obj Q ⟶ (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj)
  (hi : ∀ (T : Over S) (a : T ⟶ B), D.relativeValue a = i.app (op T) (ULift.up (a ≫ q)))

include hi in
set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.normalizedQuotientLine_universal_class :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op Q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H)) = i.app (op Q) (ULift.up (𝟙 Q)) := by
  apply FppfSheafRestriction.Construction.fppfSheaf_restriction_injective q (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A)
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op B)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H))) = _
  rw [D.normalizedQuotientLine_pullback_class q H]
  have hn := (congrArg (fun t : (uliftYoneda.{1}.obj Q).obj (op Q) ⟶
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.obj (op B) => t (ULift.up (𝟙 Q))) (i.naturality q.op)).symm
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map q.op (i.app (op Q) (ULift.up (𝟙 Q))) =
    i.app (op B) (ULift.up (q ≫ 𝟙 Q)) at hn
  rw [Category.comp_id] at hn
  rw [hn, ← D.relativeValue_id]
  simpa only [Category.id_comp] using hi B (𝟙 B)

include hi in
set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.rigidifiedQuotientLine_family_value {T : Over S} (x : T ⟶ Q) :
    (D.rigidifiedQuotientLine q H).relativeValue x = i.app (op T) (ULift.up x) := by
  have hn := (D.rigidifiedQuotientLine q H).relativeValue_natural x (𝟙 Q)
  rw [Category.comp_id, RigidifiedLine.Construction.RelativeRigidifiedProductLine.relativeValue_id] at hn
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map x.op
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.normalizedQuotientLine q H))) = _ at hn
  rw [D.normalizedQuotientLine_universal_class q H i hi] at hn
  have hm := (congrArg (fun t : (uliftYoneda.{1}.obj Q).obj (op Q) ⟶
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.obj (op T) => t (ULift.up (𝟙 Q))) (i.naturality x.op)).symm
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map x.op (i.app (op Q) (ULift.up (𝟙 Q))) =
    i.app (op T) (ULift.up (x ≫ 𝟙 Q)) at hm
  rw [Category.comp_id] at hm
  exact hn.symm.trans hm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
