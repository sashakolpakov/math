import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechHomCompatibility
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductPullbacks
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LineHomDescent

/-! # Function Normalized Picard Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctionNormalizedPicardDescent.FunctionNormalizedPicard

noncomputable section

section

/-! Normalized line comparisons descend on any abelian family whose
parameter products have exactly the parameter's functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechHomCompatibility
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard

variable {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hΓ : ∀ V : Over S, IsIso (fst V A.scheme).left.appTop)
    {T U : Over S} (u : U ⟶ T)
    (L M : (T ⊗ A.scheme).left.Modules)
    (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
    (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M)

include hΓ

theorem restrictions_eq (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) {V : Over S}
    (a b : V ⟶ U) (p : V ⟶ T) (ha : a ≫ u = p) (hb : b ≫ u = p) :
    PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.restrict A u L M eL eM a p ha e = PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.restrict A u L M eL eM b p hb e := by
  have : IsIso (fst V A.scheme).left.appTop := hΓ V
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
  have h := restrictions_eq A hΓ u L M eL eM e hL a b p rfl H.w.symm
  have hp : IsPullback (a ▷ A.scheme).left (b ▷ A.scheme).left
      (u ▷ A.scheme).left (u ▷ A.scheme).left :=
    PELModuli.IntegralModel.Picard.ProductPullbacks.PicardProductOpenCover.productMap_preserves_isPullback A.scheme a b u u H
  apply PELModuli.IntegralModel.CechHomCompatibility.compatibleHom_of_cartesian_overlap (u ▷ A.scheme).left
    (a ▷ A.scheme).left (b ▷ A.scheme).left hp (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom
    (p ▷ A.scheme).left (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.product_comp A u a p rfl) (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.product_comp A u b p H.w.symm)
  exact congrArg Iso.hom h

theorem normalize_descends [Flat u.left] [Surjective u.left] [QuasiCompact u.left]
    (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    ∃! d : L ≅ M, (Scheme.Modules.pullback (u ▷ A.scheme).left).mapIso d =
      PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e :=
  PELModuli.IntegralModel.Picard.LineHomDescent.PicardLineHomDescent.existsUnique_lineIso_descent (u ▷ A.scheme).left hL hM
    (PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e) (normalize_compatible A hΓ u L M eL eM e hL)

end

/-! Normalized native line classes are detected on an actual fpqc
parameter cover whenever the family has the proved function property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

theorem lineClass_eq_of_parameter_pullback {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hΓ : ∀ V : Over S, IsIso (fst V A.scheme).left.appTop)
    {T U : Over S} (u : U ⟶ T) [Flat u.left] [Surjective u.left] [QuasiCompact u.left]
    (L M : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (eL : (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left L).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left)
    (eM : (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left M).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf L = HilbertConstruction.Line.Bundles.LineBundle.classOf M := by
  have he : Nonempty ((HilbertConstruction.Line.Bundles.LineBundle.pullback (u ▷ A.scheme).left L).sheaf ≅
      (HilbertConstruction.Line.Bundles.LineBundle.pullback (u ▷ A.scheme).left M).sheaf) :=
    Quotient.exact (s := HilbertConstruction.Line.Bundles.LineBundle.isoSetoid _) (a := HilbertConstruction.Line.Bundles.LineBundle.pullback (u ▷ A.scheme).left L)
      (b := HilbertConstruction.Line.Bundles.LineBundle.pullback (u ▷ A.scheme).left M) h
  obtain ⟨d, _, _⟩ := normalize_descends A hΓ u L.sheaf M.sheaf eL eM he.some L.locallyTrivial M.locallyTrivial
  exact Quotient.sound ⟨d⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctionNormalizedPicardDescent.FunctionNormalizedPicard
