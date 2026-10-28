import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Dual Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback

noncomputable section

/-!
# Homomorphisms: the morphism on duals induced by actual Picard pullback

The map is constructed from the represented homogeneous Picard sheaf. Its
Poincare formula follows from that construction and the inclusion in the
full relative Picard sheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

def dualPicardPullback : E.abelian.scheme ⟶ D.abelian.scheme :=
  D.representable.homEquiv.symm
    ((HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom.app (.op E.abelian.scheme)
      (E.representable.homEquiv (𝟙 E.abelian.scheme)))

theorem dualPicardPullback_representation {T : Over S} (x : T ⟶ E.abelian.scheme) :
    D.representable.homEquiv (x ≫ dualPicardPullback D E f) =
      (HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom.app (.op T)
        (E.representable.homEquiv x) := by
  rw [D.representable.homEquiv_comp, dualPicardPullback, Equiv.apply_symm_apply]
  rw [← (HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom.naturality_apply]
  rw [← E.representable.homEquiv_comp, Category.comp_id]

theorem dualPicardPullback_poincare {T : Over S} (x : T ⟶ E.abelian.scheme) :
    PoincareDetection.Construction.poincareClass D (x ≫ dualPicardPullback D E f) =
      (SheafMaps.Construction.relativePicardPullback f).hom.app (.op T) (PoincareDetection.Construction.poincareClass E x) := by
  rw [PoincareDetection.Construction.poincareClass_eq_representation, dualPicardPullback_representation,
    PoincareDetection.Construction.poincareClass_eq_representation]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun z : B.homogeneousPicardSheaf ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme => z.hom)
      (HomogeneousPullback.Construction.homogeneousPicardPullback_inclusion A B f)) (.op T))
    (E.representable.homEquiv x)

theorem dualPicardPullback_one (T : Over S) :
    (1 : T ⟶ E.abelian.scheme) ≫ dualPicardPullback D E f = 1 := by
  apply D.representable.homEquiv.injective
  rw [dualPicardPullback_representation, E.origin, D.origin]
  exact HomogeneousPullback.Construction.homogeneousPicardPullback_trivial A B f T

theorem dualPicardPullback_unique (d : E.abelian.scheme ⟶ D.abelian.scheme)
    (hd : ∀ (T : Over S) (x : T ⟶ E.abelian.scheme),
      PoincareDetection.Construction.poincareClass D (x ≫ d) =
        (SheafMaps.Construction.relativePicardPullback f).hom.app (.op T) (PoincareDetection.Construction.poincareClass E x)) :
    d = dualPicardPullback D E f := by
  apply PoincareDetection.Construction.poincareClass_injective D E.abelian.scheme
  simpa only [Category.id_comp] using
    (hd E.abelian.scheme (𝟙 _)).trans
      (dualPicardPullback_poincare D E f (𝟙 _)).symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback
