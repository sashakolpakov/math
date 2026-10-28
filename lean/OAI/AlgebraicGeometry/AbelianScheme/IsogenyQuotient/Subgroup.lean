import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-! # Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Subgroup.Construction

noncomputable section

/-!
A geometric model of a relative subgroup carries its canonical commutative
group-scheme structure over the parameter scheme. The group laws are obtained
from the actual subgroup presheaf by Yoneda, not included as an extra field
of the geometric model. The iterated-slice equivalence then regards the result
as a group scheme over the underlying parameter scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

local instance : CartesianMonoidalCategory (Over P) := Over.cartesianMonoidalCategory P
local instance : BraidedCategory (Over P) := Over.braidedCategory P

/-- Pullback of a section of the relative subgroup along a parameter map. -/
def relativePointsPullback (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    {X Y : Over P} (f : X ⟶ Y) :
    F.points Y.left Y.hom →* F.points X.left X.hom where
  toFun a := ⟨f.left ≫ a.val, by
    have h := F.naturality f.left Y.hom a.property
    rw [f.w] at h
    exact h⟩
  map_one' := by
    apply Subtype.ext
    change f.left ≫ (1 : Y.left ⟶ A) = 1
    exact MonObj.comp_one f.left
  map_mul' a b := by
    apply Subtype.ext
    change f.left ≫ (a.val * b.val) = (f.left ≫ a.val) * (f.left ≫ b.val)
    rw [MonObj.comp_mul]

/-- The genuine presheaf of commutative groups of a relative subgroup. -/
def relativePointGroups (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    (Over P)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj X := CommGrpCat.of (F.points X.unop.left X.unop.hom)
  map f := CommGrpCat.ofHom (relativePointsPullback F f.unop)
  map_id X := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact Category.id_comp a.val
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    exact Category.assoc g.unop.left f.unop.left a.val

/-- The model's universal property is a natural representation of the
relative subgroup presheaf on the parameter's slice category. -/
def relativePointGroups_representable
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    (relativePointGroups F ⋙ forget CommGrpCat).RepresentableBy (Over.mk R.toBase) := by
  let toPoint {X : Over P} (h : X ⟶ Over.mk R.toBase) : F.points X.left X.hom :=
    ⟨h.left ≫ R.toGroup, (R.points_iff X.left X.hom _).mpr ⟨h.left, h.w, rfl⟩⟩
  have hinj (X : Over P) : Function.Injective (@toPoint X) := by
    intro h k hhk
    apply Over.OverMorphism.ext
    apply R.jointly_monic X.left
    · exact h.w.trans k.w.symm
    · exact congrArg Subtype.val hhk
  have hsurj (X : Over P) : Function.Surjective (@toPoint X) := by
    intro a
    obtain ⟨h, hbase, hgroup⟩ := (R.points_iff X.left X.hom a.val).mp a.property
    exact ⟨Over.homMk h hbase, Subtype.ext hgroup⟩
  refine {
    homEquiv := fun {X} => Equiv.ofBijective (@toPoint X) ⟨hinj X, hsurj X⟩
    homEquiv_comp := ?_
  }
  intro X X' f g
  apply Subtype.ext
  change (f.left ≫ g.left) ≫ R.toGroup = f.left ≫ (g.left ≫ R.toGroup)
  exact Category.assoc f.left g.left R.toGroup

/-- Commutativity and the group laws are constructed from the represented
point groups, using the standard Yoneda theorem for group objects. -/
def relativeModelCommGroup
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) : CommGrp (Over P) := by
  letI : CommGrpObj (Over.mk R.toBase) :=
    CommGrpObj.ofRepresentableBy (Over.mk R.toBase) (relativePointGroups F)
      (relativePointGroups_representable F R)
  exact CommGrp.mk (Over.mk R.toBase)

/-- The constructed relative subgroup is an actual commutative group
scheme over the underlying parameter scheme. -/
def subgroupGroupScheme
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) : CommGrp (Over P.left) := by
  let e := Over.iteratedSliceEquiv P
  letI : e.functor.Braided := Functor.Braided.ofChosenFiniteProducts e.functor
  exact e.functor.mapCommGrp.obj (relativeModelCommGroup F R)

/-- The group construction keeps the original finite subgroup scheme
and its structure map; no replacement by a different object is made. -/
theorem subgroupGroupScheme_structureMap
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    (subgroupGroupScheme F R).X.hom = R.toBase.left := rfl

theorem subgroupGroupScheme_finiteLocallyFree
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    IsFinite (subgroupGroupScheme F R).X.hom ∧
      Flat (subgroupGroupScheme F R).X.hom ∧
      LocallyOfFinitePresentation (subgroupGroupScheme F R).X.hom := by
  rw [subgroupGroupScheme_structureMap]
  exact ⟨R.finite, R.flat, R.finitePresentation⟩

set_option backward.isDefEq.respectTransparency false in
/-- Scheme-theoretic n-torsion of the modeled relative subgroup, obtained
from its actual point groups rather than just its geometric points. -/
theorem relativeModelCommGroup_killed
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (n : ℕ) (hkilled : F.KilledBy n) :
    (𝟙 (relativeModelCommGroup F R).X :
      (relativeModelCommGroup F R).X ⟶ (relativeModelCommGroup F R).X) ^ n = 1 := by
  let G := relativeModelCommGroup F R
  let e := yonedaGrpObjIsoOfRepresentableBy G.X
    (relativePointGroups F ⋙ forget₂ CommGrpCat GrpCat)
    (relativePointGroups_representable F R)
  apply (e.app (Opposite.op G.X)).groupIsoToMulEquiv.injective
  change (e.hom.app (Opposite.op G.X)).hom ((𝟙 G.X) ^ n) =
    (e.hom.app (Opposite.op G.X)).hom 1
  calc
    (e.hom.app (Opposite.op G.X)).hom ((𝟙 G.X) ^ n) =
        ((e.hom.app (Opposite.op G.X)).hom (𝟙 G.X)) ^ n :=
      (e.hom.app (Opposite.op G.X)).hom.map_pow _ n
    _ = 1 := by
      apply Subtype.ext
      change R.toGroup ^ n = 1
      exact R.toGroup_pow_eq_one hkilled
    _ = (e.hom.app (Opposite.op G.X)).hom 1 :=
      (e.hom.app (Opposite.op G.X)).hom.map_one.symm

open scoped _root_.CategoryTheory.Obj in
set_option backward.isDefEq.respectTransparency false in
/-- The corresponding commutative group scheme over the parameter is
killed by n as a scheme morphism. -/
theorem subgroupGroupScheme_killed
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (n : ℕ) (hkilled : F.KilledBy n) :
    (𝟙 (subgroupGroupScheme F R).X :
      (subgroupGroupScheme F R).X ⟶ (subgroupGroupScheme F R).X) ^ n = 1 := by
  let e := Over.iteratedSliceEquiv P
  let _ : e.functor.Braided := Functor.Braided.ofChosenFiniteProducts e.functor
  let G := relativeModelCommGroup F R
  let m : (G.X ⟶ G.X) →* (e.functor.obj G.X ⟶ e.functor.obj G.X) :=
    e.functor.homMonoidHom
  have h := congrArg m (relativeModelCommGroup_killed F R n hkilled)
  have hpow : (m (𝟙 G.X)) ^ n = 1 := by simpa only [map_pow, map_one] using h
  change (e.functor.map (𝟙 G.X)) ^ n = 1 at hpow
  rw [e.functor.map_id] at hpow
  exact hpow

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Subgroup.Construction
