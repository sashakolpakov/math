import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Unbundled Dual Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback

noncomputable section

/-! Dimension-independent dual pullback,
using the actual line bundles and represented homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (E : UnbundledDualData.Construction.UnbundledPicard.DualData B)
  (f : A ⟶ B) [IsMonHom f]

def dualPicardPullback : E.abelian ⟶ D.abelian :=
  D.representable.homEquiv.symm
    ((UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (.op E.abelian)
      (E.representable.homEquiv (𝟙 E.abelian)))

theorem dualPicardPullback_representation {T : Over S} (x : T ⟶ E.abelian) :
    D.representable.homEquiv (x ≫ dualPicardPullback D E f) =
      (UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (.op T)
        (E.representable.homEquiv x) := by
  rw [D.representable.homEquiv_comp, dualPicardPullback, Equiv.apply_symm_apply]
  rw [← (UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.naturality_apply]
  rw [← E.representable.homEquiv_comp, Category.comp_id]

theorem dualPicardPullback_poincare {T : Over S} (x : T ⟶ E.abelian) :
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (x ≫ dualPicardPullback D E f) =
      (SheafMaps.Construction.relativePicardPullback f).hom.app (.op T) (UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass E x) := by
  rw [UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation, dualPicardPullback_representation,
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun z : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B) ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A => z.hom)
      (UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_inclusion A B f)) (.op T))
    (E.representable.homEquiv x)

theorem dualPicardPullback_one (T : Over S) :
    (1 : T ⟶ E.abelian) ≫ dualPicardPullback D E f = 1 := by
  apply D.representable.homEquiv.injective
  rw [dualPicardPullback_representation, E.origin, D.origin]
  exact UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_trivial A B f T

theorem dualPicardPullback_unique (d : E.abelian ⟶ D.abelian)
    (hd : ∀ (T : Over S) (x : T ⟶ E.abelian),
      UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (x ≫ d) =
        (SheafMaps.Construction.relativePicardPullback f).hom.app (.op T) (UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass E x)) :
    d = dualPicardPullback D E f := by
  apply UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_injective D E.abelian
  simpa only [Category.id_comp] using
    (hd E.abelian (𝟙 _)).trans
      (dualPicardPullback_poincare D E f (𝟙 _)).symm

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback
