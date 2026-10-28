import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Local Isomorphisms Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs

noncomputable section

/-!
# CartierDuality: detecting native group isomorphisms on an open cover of the base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v

namespace Construction

namespace LocalIsomorphisms

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- A map between two objects over a base has the expected cartesian
square after applying the native pullback functor. -/
theorem pullbackMap_isPullback {S T : C} (f : T ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map g).left
      g.left (pullback.fst Y.hom f) := by
  have hs : IsPullback (pullback.fst X.hom f)
      (((Over.pullback f).map g).left ≫ pullback.snd Y.hom f) (g.left ≫ Y.hom) f := by
    rw [g.w]
    have hp : ((Over.pullback f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
      pullback.lift_snd _ _ _
    rw [hp]
    exact .of_hasPullback _ _
  exact hs.of_bot (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback Y.hom f)

end LocalIsomorphisms

namespace Schemes

/-- Isomorphisms of objects over a scheme can be checked on an open
cover of the base, using the native pullback maps. -/
theorem overMap_isIso_of_openCover {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y)
    (𝒰 : S.OpenCover) (h : ∀ i, IsIso ((Over.pullback (𝒰.f i)).map g)) : IsIso g := by
  have hg : IsIso g.left := by
    change MorphismProperty.isomorphisms Scheme g.left
    apply (MorphismProperty.isomorphisms Scheme).of_zeroHypercover_target (𝒰.pullback₁ Y.hom)
    intro i
    have hi := h i
    have hm : IsIso (((Over.pullback (𝒰.f i)).map g).left) :=
      inferInstanceAs (IsIso ((Over.forget (𝒰.X i)).map ((Over.pullback (𝒰.f i)).map g)))
    let sq := LocalIsomorphisms.pullbackMap_isPullback (𝒰.f i) g
    change IsIso (pullback.snd g.left (pullback.fst Y.hom (𝒰.f i)))
    exact sq.isoPullback_inv_snd ▸ inferInstanceAs
      (IsIso (sq.isoPullback.inv ≫ ((Over.pullback (𝒰.f i)).map g).left))
  let : IsIso ((Over.forget S).map g) := hg
  exact isIso_of_reflects_iso g (Over.forget S)

/-- A native group morphism is an isomorphism if its pullbacks along
an open cover of the base are isomorphisms. -/
theorem groupMap_isIso_of_openCover {S : Scheme.{u}} {G H : Grp (Over S)} (g : G ⟶ H)
    (𝒰 : S.OpenCover) (h : ∀ i, IsIso ((Over.pullback (𝒰.f i)).mapGrp.map g)) : IsIso g := by
  have hg : IsIso g.hom.hom := overMap_isIso_of_openCover g.hom.hom 𝒰 (fun i => by
    have hi := h i
    exact inferInstanceAs (IsIso ((Grp.forget (Over (𝒰.X i))).map
      ((Over.pullback (𝒰.f i)).mapGrp.map g))))
  let e : G ≅ H := Grp.mkIso (asIso g.hom.hom)
  have he : e.hom = g := by
    apply Grp.hom_ext
    rfl
  exact he ▸ e.isIso_hom

end Schemes

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs
