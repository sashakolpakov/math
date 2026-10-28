import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass

/-! # Dual Poincare Class -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareClass

noncomputable section

/-! The constructed dual morphism has the actual normalized Poincare
line-bundle identity over an algebraically closed field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] [IsAlgClosed k] {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem dualPicardPullback_actual_poincare :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f ⊗ₘ 𝟙 A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) := by
  let : CompactSpace DB.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace DB.abelian.scheme.hom
  let : QuasiSeparatedSpace DB.abelian.scheme.left :=
    quasiSeparatedSpace_of_quasiSeparated DB.abelian.scheme.hom
  let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f ⊗ₘ 𝟙 A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)
  let r := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)
  have he := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB f (𝟙 DB.abelian.scheme)
  rw [Category.id_comp, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at he
  have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme) q =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme) r := by
    simpa only [q, r, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass, tensorHom_id, id_tensorHom,
      Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf, TypeCat.ofHom_apply] using he
  have hq : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme).left q = 1 := by
    dsimp only [q]
    rw [tensorHom_id]
    exact PoincareClass.PoincareClasses.familyClass_zero DA (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f)
  have hfzero : Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme ≫ (𝟙 DB.abelian.scheme ⊗ₘ f) =
      Isogenies.NeighborCounting.PoincareNormalization.familyZero B DB.abelian.scheme := by
    simp [Isogenies.NeighborCounting.PoincareNormalization.familyZero]
  have hr : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme).left r = 1 := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) = 1
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, hfzero]
    exact Quotient.sound DB.normalizedAtAbelianZero
  exact (Picard.Inv.NormalizedPicard.normalizedClass_eq_self A DB.abelian.scheme q hq).symm.trans
    ((Picard.Inv.NormalizedPicard.normalizedClass_eq_of_picard_eq A q r hrel).trans
      (Picard.Inv.NormalizedPicard.normalizedClass_eq_self A DB.abelian.scheme r hr))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareClass
