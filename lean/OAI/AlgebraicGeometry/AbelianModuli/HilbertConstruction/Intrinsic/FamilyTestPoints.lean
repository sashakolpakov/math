import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Family Test Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints

noncomputable section

/-! Points of a native family over a test scheme are exactly
sections of its actual pulled-back family. This equivalence comes
from the Cartesian family square and retains the projection formulas. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} (X : Over S) {T U : Over S}

def nativeFamilyOver (T : Over S) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) : Over T.left :=
  Over.mk (HilbertScheme.Presentations.Hilbert.Functor.familyProjection X F.val)

variable (a : U ⟶ T) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T)

def nativeFamilyPointPullback :
    (Over.mk a.left ⟶ nativeFamilyOver X T F) ≃
      (Over.mk (𝟙 U.left) ⟶ nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)) where
  toFun x := Over.homMk
    ((HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).lift (𝟙 U.left) x.left
      ((Category.id_comp _).trans x.w.symm))
    ((HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).lift_fst _ _ _)
  invFun y := Over.homMk (y.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) (by
    change (y.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) ≫ HilbertScheme.Presentations.Hilbert.Functor.familyProjection X F.val = a.left
    erw [Category.assoc, ← (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).w, ← Category.assoc, y.w, Category.id_comp])
  left_inv x := by
    apply Over.OverMorphism.ext
    exact (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).lift_snd _ _ _
  right_inv y := by
    apply Over.OverMorphism.ext
    apply (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).hom_ext
    · exact ((HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).lift_fst _ _ _).trans y.w.symm
    · exact (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).lift_snd _ _ _

theorem nativeFamilyPointPullback_projection (x : Over.mk a.left ⟶ nativeFamilyOver X T F) :
    (nativeFamilyPointPullback X a F x).left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val = x.left :=
  (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).lift_snd _ _ _

theorem nativeFamilyPointPullback_symm_left
    (y : Over.mk (𝟙 U.left) ⟶ nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)) :
    ((nativeFamilyPointPullback X a F).symm y).left = y.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val := rfl

variable (G : HilbertScheme.Presentations.Hilbert.Functor.Family X T)

def nativeFamilyTestPointTransport
    (e : nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≅
      nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G)) :
    (Over.mk a.left ⟶ nativeFamilyOver X T F) ≃ (Over.mk a.left ⟶ nativeFamilyOver X T G) :=
  (nativeFamilyPointPullback X a F).trans
    ((Iso.homCongr (Iso.refl _) e).trans (nativeFamilyPointPullback X a G).symm)

theorem nativeFamilyTestPointTransport_left
    (e : nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F) ≅
      nativeFamilyOver X U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G))
    (x : Over.mk a.left ⟶ nativeFamilyOver X T F) :
    (nativeFamilyTestPointTransport X a F G e x).left =
      (nativeFamilyPointPullback X a F x).left ≫ e.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val := by
  change ((𝟙 _) ≫ (nativeFamilyPointPullback X a F x).left ≫ e.hom.left) ≫
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val = _
  simp only [Category.id_comp]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints
