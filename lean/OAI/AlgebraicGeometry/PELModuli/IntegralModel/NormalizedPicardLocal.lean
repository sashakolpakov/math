import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedZeroComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality

/-! # Normalized Picard Local -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard

noncomputable section

/-! Normalize arbitrary local comparisons of line bundles on an abelian
product family. Their restrictions are unique on all parameter schemes,
including nonreduced ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {T U : Over S} (u : U ⟶ T)
  (L M : (T ⊗ A.scheme).left.Modules)
  (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
  (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)

def localZeroIso (L : (T ⊗ A.scheme).left.Modules)
    (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left) :
    (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left).obj
      ((Scheme.Modules.pullback (u ▷ A.scheme).left).obj L) ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.left :=
  Picard.NormalizedSquares.PicardNormalizedSquares.squareZeroIso (u ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left u.left (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u)) eL

def normalize
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M) :
    (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M :=
  Isogenies.NeighborCounting.RigidifiedIso.normalizedIso (fst U A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left e
    (localZeroIso A u L eL) (localZeroIso A u M eM)

theorem normalize_section
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M) :
    (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left).map (normalize A u L M eL eM e).hom ≫
      (Picard.NormalizedSquares.PicardNormalizedSquares.squareZeroIso (u ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
        (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left u.left (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u)) eM).hom =
      (Picard.NormalizedSquares.PicardNormalizedSquares.squareZeroIso (u ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
        (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left u.left (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u)) eL).hom :=
  Isogenies.NeighborCounting.RigidifiedIso.normalizedIso_section (fst U A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A U) e (localZeroIso A u L eL) (localZeroIso A u M eM)

theorem normalize_intrinsic
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M) :
    Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left u.left (u ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u))
      (normalize A u L M eL eM e).hom (eL.hom ≫ eM.inv) :=
  Picard.NormalizedZeroComparison.PicardNormalizedZeroComparison.normalized_zero_intrinsic (u ▷ A.scheme).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left u.left
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u)) eL eM _ (normalize_section A u L M eL eM e)

omit L M eL eM in
theorem product_comp {V : Over S} (a : V ⟶ U) (p : V ⟶ T) (ha : a ≫ u = p) :
    (a ▷ A.scheme).left ≫ (u ▷ A.scheme).left = (p ▷ A.scheme).left :=
  ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map_comp a u).symm.trans
    (congrArg (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map ha)

def restrict {V : Over S} (a : V ⟶ U) (p : V ⟶ T) (ha : a ≫ u = p)
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M) :
    (Scheme.Modules.pullback (p ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (p ▷ A.scheme).left).obj M :=
  Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo (a ▷ A.scheme).left (u ▷ A.scheme).left (p ▷ A.scheme).left
    (product_comp A u a p ha) (normalize A u L M eL eM e)

theorem restrict_intrinsic {V : Over S} (a : V ⟶ U) (p : V ⟶ T) (ha : a ≫ u = p)
    (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M) :
    Isogenies.NeighborCounting.NormalizationRestriction.IsNormalized (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left p.left (p ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A p))
      (restrict A u L M eL eM a p ha e).hom (eL.hom ≫ eM.inv) :=
  Picard.NormalizedZeroComparison.PicardNormalizedZeroComparison.intrinsic_normalization_restrict_iso (u ▷ A.scheme).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left u.left
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A u))
    (normalize A u L M eL eM e) (eL.hom ≫ eM.inv) (normalize_intrinsic A u L M eL eM e)
    (a ▷ A.scheme).left a.left p.left (p ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left
    (congrArg Over.Hom.left ha) (product_comp A u a p ha)
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a))
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A p))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard
