import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle

/-! # Poincare Family Compatibility -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareFamilyCompatibility.Family

noncomputable section

/-! The normalized Poincare comparison agrees on every pair of test
families with the same map to the dual base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedZeroComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom

variable {k : Type u} [Field k] [IsAlgClosed k] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

omit [IsAlgClosed k] in
theorem product_comp {T V : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (v : V ⟶ T) (p : V ⟶ DB.abelian.scheme) (h : v ≫ t = p) :
    (v ▷ A.scheme).left ≫ (t ▷ A.scheme).left = (p ▷ A.scheme).left :=
  ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map_comp v t).symm.trans
    (congrArg (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map h)

def commonRestriction {T V : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t)
    (v : V ⟶ T) (p : V ⟶ DB.abelian.scheme) (h : v ≫ t = p) :
    (PoincareNormalization.abelianLocalBundle DB f p).sheaf ≅ (PoincareNormalization.dualLocalBundle DA DB f p).sheaf :=
  FramedPullback.pullbackIsoTo (v ▷ A.scheme).left (t ▷ A.scheme).left (p ▷ A.scheme).left
    (product_comp DB t v p h) (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht)

omit [IsAlgClosed k] in
theorem commonRestriction_normalized {T V : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t)
    (v : V ⟶ T) (p : V ⟶ DB.abelian.scheme) (h : v ≫ t = p) :
    NormalizationRestriction.IsNormalized (F := ModulePullbackHom.modulePullbackFunctor)
      (PoincareNormalization.familyZero A DB.abelian.scheme).left p.left (p ▷ A.scheme).left (PoincareNormalization.familyZero A V).left
      (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A p))
      (commonRestriction DA DB f t ht v p h).hom (PoincareCocycle.globalZeroComparison DA DB f) :=
  NormalizedZeroComparison.intrinsic_normalization_restrict_iso
    (M := (PoincareCocycle.abelianGlobalBundle DB f).sheaf) (N := (PoincareCocycle.dualGlobalBundle DA DB f).sheaf)
    (t ▷ A.scheme).left (PoincareNormalization.familyZero A DB.abelian.scheme).left (PoincareNormalization.familyZero A T).left t.left
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A t))
    (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht) (PoincareCocycle.globalZeroComparison DA DB f)
    (PoincareCocycle.poincareLocal_intrinsic DA DB f t ht)
    (v ▷ A.scheme).left v.left p.left (p ▷ A.scheme).left (PoincareNormalization.familyZero A V).left
    (congrArg Over.Hom.left h) (product_comp DB t v p h)
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A v))
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A p))

theorem commonRestrictions_eq {T V : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t)
    (x y : V ⟶ T) (p : V ⟶ DB.abelian.scheme) (hx : x ≫ t = p) (hy : y ≫ t = p) :
    commonRestriction DA DB f t ht x p hx = commonRestriction DA DB f t ht y p hy := by
  have : IsIntegral A.scheme.left :=
    AbelianScheme.HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected A.scheme.hom
  have hΓ : IsIso ((fst V A.scheme).left.appTop) := ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections.Construction.isIso_properBaseChange_app V A.scheme ⊤
  exact NormalizedZeroComparison.iso_eq_of_intrinsic_normalization (p ▷ A.scheme).left
    (PoincareNormalization.familyZero A DB.abelian.scheme).left (PoincareNormalization.familyZero A V).left p.left
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A p))
    (fst V A.scheme).left (PoincareNormalization.familyZero_projection A V)
    (ConcreteCategory.bijective_of_isIso ((fst V A.scheme).left.appTop)).surjective
    (PoincareNormalization.abelianLocalBundle DB f p).locallyTrivial _ _ (PoincareCocycle.globalZeroComparison DA DB f)
    (commonRestriction_normalized DA DB f t ht x p hx)
    (commonRestriction_normalized DA DB f t ht y p hy)

theorem poincareFamily_compatible {T V : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t)
    (x y : V ⟶ T) (p : V ⟶ DB.abelian.scheme) (hx : x ≫ t = p) (hy : y ≫ t = p) :
    FramedPullback.pullbackHomTo (x ▷ A.scheme).left (t ▷ A.scheme).left (p ▷ A.scheme).left
        (product_comp DB t x p hx) (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht).hom =
      FramedPullback.pullbackHomTo (y ▷ A.scheme).left (t ▷ A.scheme).left (p ▷ A.scheme).left
        (product_comp DB t y p hy) (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht).hom := by
  exact (FramedPullback.pullbackIsoTo_hom (x ▷ A.scheme).left (t ▷ A.scheme).left (p ▷ A.scheme).left
    (product_comp DB t x p hx) (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht)).symm.trans
      ((congrArg Iso.hom (commonRestrictions_eq DA DB f t ht x y p hx hy)).trans
        (FramedPullback.pullbackIsoTo_hom (y ▷ A.scheme).left (t ▷ A.scheme).left (p ▷ A.scheme).left
          (product_comp DB t y p hy) (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareFamilyCompatibility.Family
