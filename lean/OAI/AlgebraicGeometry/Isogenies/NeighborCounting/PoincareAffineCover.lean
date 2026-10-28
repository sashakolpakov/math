import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductOpenCover
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OverFiniteFppfCover

/-! # Poincare Affine Cover -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareAffineCover

noncomputable section

/-! The derived Poincare comparison sieve contains an actual affine fpqc
covering arrow. Its comparison is assembled from a finite affine refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OverFiniteFppfCover OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductOpenCover

variable {k : Type u} [Field k] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

local instance dual_compact : CompactSpace DB.abelian.scheme.left :=
  QuasiCompact.compactSpace_of_compactSpace DB.abelian.scheme.hom

local instance dual_quasiSeparated : QuasiSeparatedSpace DB.abelian.scheme.left :=
  quasiSeparatedSpace_of_quasiSeparated DB.abelian.scheme.hom

def finiteCover : FiniteFppfCover.Family DB.abelian.scheme.left
    (Sieve.overEquiv DB.abelian.scheme (PoincareLocal.poincareComparisonCover DA DB f).1) :=
  OverFiniteFppfCover.underlyingFamily (PoincareLocal.poincareComparisonCover DA DB f).2

def affineCoverObject : Over (Spec (.of k)) := OverFiniteFppfCover.coverTotal (finiteCover DA DB f)

def affineCoverMap : affineCoverObject DA DB f ⟶ DB.abelian.scheme :=
  OverFiniteFppfCover.coverProjection (finiteCover DA DB f)

theorem component_comp (i : Fin (finiteCover DA DB f).n) :
    (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f) i ▷ A.scheme).left ≫
        (affineCoverMap DA DB f ▷ A.scheme).left =
      (OverFiniteFppfCover.coverMap (finiteCover DA DB f) i ▷ A.scheme).left :=
  ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map_comp (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f) i)
      (affineCoverMap DA DB f)).symm.trans
    (congrArg (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor A.scheme).map
      (OverFiniteFppfCover.coverInclusion_projection (finiteCover DA DB f) i))

def componentIso (i : Fin (finiteCover DA DB f).n) :
    (Scheme.Modules.pullback (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f) i ▷ A.scheme).left).obj
        (PoincareNormalization.abelianLocalBundle DB f (affineCoverMap DA DB f)).sheaf ≅
      (Scheme.Modules.pullback (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f) i ▷ A.scheme).left).obj
        (PoincareNormalization.dualLocalBundle DA DB f (affineCoverMap DA DB f)).sheaf :=
  ((Scheme.Modules.pullbackComp (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f) i ▷ A.scheme).left
        (affineCoverMap DA DB f ▷ A.scheme).left ≪≫
      Scheme.Modules.pullbackCongr (component_comp DA DB f i)).app (PoincareCocycle.abelianGlobalBundle DB f).sheaf) ≪≫
    PoincareLocal.poincareLocalIso DA DB f (OverFiniteFppfCover.coverMap (finiteCover DA DB f) i)
      (OverFiniteFppfCover.coverMap_member (finiteCover DA DB f) i) ≪≫
    ((Scheme.Modules.pullbackComp (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f) i ▷ A.scheme).left
        (affineCoverMap DA DB f ▷ A.scheme).left ≪≫
      Scheme.Modules.pullbackCongr (component_comp DA DB f i)).app (PoincareCocycle.dualGlobalBundle DA DB f).sheaf).symm

theorem exists_affineCoverIso : Nonempty
    ((PoincareNormalization.abelianLocalBundle DB f (affineCoverMap DA DB f)).sheaf ≅
      (PoincareNormalization.dualLocalBundle DA DB f (affineCoverMap DA DB f)).sheaf) := by
  obtain ⟨e, _, _⟩ := ProductOpenCover.existsUnique_disjoint_product_iso A.scheme
    (OverFiniteFppfCover.coverObject (finiteCover DA DB f)) (OverFiniteFppfCover.coverInclusion (finiteCover DA DB f))
    (OverFiniteFppfCover.coverInclusion_covers (finiteCover DA DB f)) (OverFiniteFppfCover.coverInclusion_disjoint (finiteCover DA DB f))
    (componentIso DA DB f)
  exact ⟨e⟩

def affineCoverIso : (PoincareNormalization.abelianLocalBundle DB f (affineCoverMap DA DB f)).sheaf ≅
    (PoincareNormalization.dualLocalBundle DA DB f (affineCoverMap DA DB f)).sheaf :=
  Classical.choice (exists_affineCoverIso DA DB f)

theorem affineCoverMap_member : (PoincareLocal.poincareComparisonCover DA DB f).1 (affineCoverMap DA DB f) := by
  apply Subtype.ext
  exact Quotient.sound ⟨affineCoverIso DA DB f⟩

instance affineCoverObject_affine : IsAffine (affineCoverObject DA DB f).left :=
  inferInstanceAs (IsAffine (OverFiniteFppfCover.coverTotal (finiteCover DA DB f)).left)

instance affineCoverMap_flat : Flat (affineCoverMap DA DB f).left :=
  inferInstanceAs (Flat (OverFiniteFppfCover.coverProjection (finiteCover DA DB f)).left)

instance affineCoverMap_surjective : Surjective (affineCoverMap DA DB f).left :=
  inferInstanceAs (Surjective (OverFiniteFppfCover.coverProjection (finiteCover DA DB f)).left)

instance affineCoverMap_quasiCompact : QuasiCompact (affineCoverMap DA DB f).left :=
  inferInstanceAs (QuasiCompact (OverFiniteFppfCover.coverProjection (finiteCover DA DB f)).left)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareAffineCover
