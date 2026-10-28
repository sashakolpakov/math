import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! # Dual Poincare Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareBaseChange

noncomputable section

/-! Actual Poincare duality for endomorphisms defined on parameter
families obtained from a geometric abelian variety. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

section General
variable {S : Scheme} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (u : A.scheme ⟶ B.scheme) [IsMonHom u]

theorem dualPicardPullback_normalized_left :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB u ⊗ₘ 𝟙 A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) = 1 := by
  rw [tensorHom_id]
  have hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DA.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) = 1 := Quotient.sound DA.normalizedAtAbelianZero
  have h := Picard.Inv.NormalizedPicard.zero_class_naturality A (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB u) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)
  rw [hzero, map_one] at h
  exact h

theorem dualPicardPullback_normalized_right :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ u).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) = 1 := by
  have hzero : Isogenies.NeighborCounting.PoincareNormalization.familyZero A DB.abelian.scheme ≫ (𝟙 DB.abelian.scheme ⊗ₘ u) =
      Isogenies.NeighborCounting.PoincareNormalization.familyZero B DB.abelian.scheme := by simp [Isogenies.NeighborCounting.PoincareNormalization.familyZero]
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, hzero]
  exact Quotient.sound DB.normalizedAtAbelianZero

theorem dualPicardPullback_actual_classes_in_picard :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB u ⊗ₘ 𝟙 A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ u).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) := by
  have he := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB u (𝟙 DB.abelian.scheme)
  rw [Category.id_comp, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id, Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at he
  simpa only [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass, tensorHom_id, id_tensorHom,
    Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf, TypeCat.ofHom_apply] using he
end General

theorem dualPicardPullback_actual_poincare_after_baseChange
    {k : Type} [Field k] [IsAlgClosed k] {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) {S : Scheme} (f : S ⟶ Spec (.of k))
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (A.pullback f)) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    [CompactSpace DB.abelian.scheme.left] [QuasiSeparatedSpace DB.abelian.scheme.left]
    (u : (A.pullback f).scheme ⟶ B.scheme) [IsMonHom u] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB u ⊗ₘ 𝟙 (A.pullback f).scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ u).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) :=
  Picard.Inv.NormalizedPicard.class_eq_of_picard_eq_after_baseChange A f DB.abelian.scheme _ _
    (dualPicardPullback_normalized_left DA DB u)
    (dualPicardPullback_normalized_right DB u)
    (dualPicardPullback_actual_classes_in_picard DA DB u)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareBaseChange
