import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareUniqueness
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedZeroComparison

/-! # Poincare Cocycle -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle

noncomputable section

/-! Intrinsic normalization and restriction of the constructed Poincare
comparison on its derived covering sieve. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedZeroComparison

variable {k : Type u} [Field k] [IsAlgClosed k] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

abbrev abelianGlobalBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (DB.abelian.scheme ⊗ A.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DB.abelian.scheme ◁ f).left DB.poincare

abbrev dualGlobalBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (DB.abelian.scheme ⊗ A.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualComparison.dualMap DA DB f ▷ A.scheme).left DA.poincare

def globalZeroComparison :
    (Scheme.Modules.pullback (PoincareNormalization.familyZero A DB.abelian.scheme).left).obj
        (abelianGlobalBundle DB f).sheaf ⟶
      (Scheme.Modules.pullback (PoincareNormalization.familyZero A DB.abelian.scheme).left).obj
        (dualGlobalBundle DA DB f).sheaf :=
  (PoincareNormalization.abelianGlobalZeroIso DB f).hom ≫ (PoincareNormalization.dualGlobalZeroIso DA DB f).inv

omit [IsAlgClosed k] in
theorem poincareLocal_intrinsic {T : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) :
    NormalizationRestriction.IsNormalized (F := ModulePullbackHom.modulePullbackFunctor)
      (PoincareNormalization.familyZero A DB.abelian.scheme).left t.left (t ▷ A.scheme).left (PoincareNormalization.familyZero A T).left
      (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A t))
      (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht).hom (globalZeroComparison DA DB f) :=
  NormalizedZeroComparison.normalized_zero_intrinsic (t ▷ A.scheme).left (PoincareNormalization.familyZero A DB.abelian.scheme).left
    (PoincareNormalization.familyZero A T).left t.left (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A t))
    (PoincareNormalization.abelianGlobalZeroIso DB f) (PoincareNormalization.dualGlobalZeroIso DA DB f) _
    (PoincareNormalization.normalizedPoincareLocalIso_section DA DB f t ht)

def poincareRestriction {T U : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) (v : U ⟶ T) :
    (PoincareNormalization.abelianLocalBundle DB f (v ≫ t)).sheaf ≅ (PoincareNormalization.dualLocalBundle DA DB f (v ≫ t)).sheaf :=
  FramedPullback.pullbackIsoTo (v ▷ A.scheme).left (t ▷ A.scheme).left ((v ≫ t) ▷ A.scheme).left
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map_comp v t).symm (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht)

omit [IsAlgClosed k] in
theorem poincareRestriction_intrinsic {T U : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) (v : U ⟶ T) :
    NormalizationRestriction.IsNormalized (F := ModulePullbackHom.modulePullbackFunctor)
      (PoincareNormalization.familyZero A DB.abelian.scheme).left (v ≫ t).left ((v ≫ t) ▷ A.scheme).left
      (PoincareNormalization.familyZero A U).left (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A (v ≫ t)))
      (poincareRestriction DA DB f t ht v).hom (globalZeroComparison DA DB f) := by
  have hs : (v ▷ A.scheme).left ≫ (t ▷ A.scheme).left = ((v ≫ t) ▷ A.scheme).left :=
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map_comp v t).symm
  exact NormalizedZeroComparison.intrinsic_normalization_restrict_iso
    (M := (abelianGlobalBundle DB f).sheaf) (N := (dualGlobalBundle DA DB f).sheaf)
    (t ▷ A.scheme).left
    (PoincareNormalization.familyZero A DB.abelian.scheme).left (PoincareNormalization.familyZero A T).left t.left
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A t))
    (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht) (globalZeroComparison DA DB f)
    (poincareLocal_intrinsic DA DB f t ht)
    (v ▷ A.scheme).left v.left (v ≫ t).left ((v ≫ t) ▷ A.scheme).left (PoincareNormalization.familyZero A U).left
    rfl hs (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A v))
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A (v ≫ t)))

/-- The constructed normalized local isomorphisms agree with actual
pullback to every further cover member. This supplies the overlap maps. -/
theorem poincareLocalIso_pullback {T U : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) (v : U ⟶ T) :
    poincareRestriction DA DB f t ht v =
      PoincareNormalization.normalizedPoincareLocalIso DA DB f (v ≫ t)
        ((PoincareLocal.poincareComparisonCover DA DB f).1.downward_closed ht v) := by
  have : IsIntegral A.scheme.left :=
    AbelianScheme.HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected A.scheme.hom
  have hΓ : IsIso ((fst U A.scheme).left.appTop) := ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections.Construction.isIso_properBaseChange_app U A.scheme ⊤
  exact NormalizedZeroComparison.iso_eq_of_intrinsic_normalization ((v ≫ t) ▷ A.scheme).left
    (PoincareNormalization.familyZero A DB.abelian.scheme).left (PoincareNormalization.familyZero A U).left (v ≫ t).left
    (congrArg Over.Hom.left (PoincareNormalization.familyZero_naturality A (v ≫ t)))
    (fst U A.scheme).left (PoincareNormalization.familyZero_projection A U)
    (ConcreteCategory.bijective_of_isIso ((fst U A.scheme).left.appTop)).surjective
    (PoincareNormalization.abelianLocalBundle DB f (v ≫ t)).locallyTrivial _ _ (globalZeroComparison DA DB f)
    (poincareRestriction_intrinsic DA DB f t ht v)
    (poincareLocal_intrinsic DA DB f (v ≫ t)
      ((PoincareLocal.poincareComparisonCover DA DB f).1.downward_closed ht v))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle
