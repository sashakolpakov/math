import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PicardFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechHomCompatibility
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductPullbacks

/-! # Normalized Picard Overlap -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.NormalizedPicardOverlap.RelativeNormalizedPicard

noncomputable section

/-! Normalized local comparisons agree on arbitrary Cech overlaps of
an abelian family over a locally noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechHomCompatibility
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {T U : Over S} (u : U ⟶ T)
  (L M : (T ⊗ A.scheme).left.Modules)
  (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
  (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
  (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
    (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M)

theorem restrictions_eq (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) {V : Over S}
    (a b : V ⟶ U) (p : V ⟶ T) (ha : a ≫ u = p) (hb : b ≫ u = p) :
    PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.restrict A u L M eL eM a p ha e = PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.restrict A u L M eL eM b p hb e := by
  have hΓ : IsIso (fst V A.scheme).left.appTop :=
    PicardFunctions.RelativePicardFunctions.isIso_product_app A V ⊤
  exact PELModuli.IntegralModel.Picard.NormalizedZeroComparison.PicardNormalizedZeroComparison.iso_eq_of_intrinsic_normalization
    (p ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left p.left
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A p))
    (fst V A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A V)
    (ConcreteCategory.bijective_of_isIso (fst V A.scheme).left.appTop).surjective
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback (p ▷ A.scheme).left L hL)
    _ _ (eL.hom ≫ eM.inv)
    (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.restrict_intrinsic A u L M eL eM a p ha e)
    (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.restrict_intrinsic A u L M eL eM b p hb e)

theorem normalize_compatible (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) :
    Isogenies.NeighborCounting.FramedDescent.CompatibleHom (u ▷ A.scheme).left (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom := by
  let a : CategoryTheory.Limits.pullback u u ⟶ U := CategoryTheory.Limits.pullback.fst u u
  let b : CategoryTheory.Limits.pullback u u ⟶ U := CategoryTheory.Limits.pullback.snd u u
  let p := a ≫ u
  have H : IsPullback a b u u := IsPullback.of_hasPullback u u
  have h := restrictions_eq A u L M eL eM e hL a b p rfl H.w.symm
  have hp : IsPullback (a ▷ A.scheme).left (b ▷ A.scheme).left
      (u ▷ A.scheme).left (u ▷ A.scheme).left := by
    exact PELModuli.IntegralModel.Picard.ProductPullbacks.PicardProductOpenCover.productMap_preserves_isPullback A.scheme a b u u H
  apply PELModuli.IntegralModel.CechHomCompatibility.compatibleHom_of_cartesian_overlap (u ▷ A.scheme).left
    (a ▷ A.scheme).left (b ▷ A.scheme).left hp (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom
    (p ▷ A.scheme).left (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.product_comp A u a p rfl) (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.product_comp A u b p H.w.symm)
  exact congrArg Iso.hom h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.NormalizedPicardOverlap.RelativeNormalizedPicard
