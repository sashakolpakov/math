import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.NormalizedPicardInjection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity

/-! # Poincare Pullback -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PoincarePullback

noncomputable section

/-! The actual Picard dual map preserves the independently specified
normalized Poincare bundles over the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] {a b : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem poincare_relativeClass_eq :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DualComparison.dualMap DA DB f ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) := by
  have hl := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Picard.Homomorphisms.PoincareDetection.Construction.homogeneousPicardSheafInclusion_toSheafify A) (op DB.abelian.scheme))
      (PoincareLocal.abelianPullClass DB f)
  have hr := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Picard.Homomorphisms.PoincareDetection.Construction.homogeneousPicardSheafInclusion_toSheafify A) (op DB.abelian.scheme))
      (PoincareLocal.dualPullClass DA DB f)
  exact hl.symm.trans ((congrArg (A.homogeneousPicardSheafInclusion.hom.app (op DB.abelian.scheme))
    (PoincareLocal.poincare_sheafification_eq DA DB f)).trans hr)

theorem poincareClass_eq :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DualComparison.dualMap DA DB f ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) := by
  have : CompactSpace DB.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace DB.abelian.scheme.hom
  have : QuasiSeparatedSpace DB.abelian.scheme.left :=
    quasiSeparatedSpace_of_quasiSeparated DB.abelian.scheme.hom
  exact NormalizedPicardInjection.class_eq_of_picard_eq A
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DB.abelian.scheme ◁ f).left DB.poincare)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualComparison.dualMap DA DB f ▷ A.scheme).left DA.poincare)
    (PoincareNormalization.abelianGlobalZeroIso DB f) (PoincareNormalization.dualGlobalZeroIso DA DB f)
    (poincare_relativeClass_eq DA DB f)

theorem dualMap_eq_native : DualComparison.dualMap DA DB f = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  apply AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare
  simpa only [id_tensorHom, tensorHom_id] using (poincareClass_eq DA DB f).symm

theorem nativeDualMap_poincare :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB ⊗ₘ 𝟙 A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) := by
  simpa only [id_tensorHom, tensorHom_id, dualMap_eq_native] using (poincareClass_eq DA DB f).symm

theorem nativeDualMap_isMonHom : IsMonHom (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB) := by
  apply AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction.pointed_isMonHom_over_reduced_base DB.abelian.scheme DA.abelian.scheme
  simpa only [MonObj.one_eq_one] using
    AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_one f DA DB (𝟙_ (Over (Spec (.of k))))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PoincarePullback
