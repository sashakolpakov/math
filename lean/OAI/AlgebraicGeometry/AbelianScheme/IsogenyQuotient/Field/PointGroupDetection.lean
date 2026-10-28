import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointwiseFiberRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Point Group Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PointGroupDetection.Construction

noncomputable section

/-! Field base changes detect values on field-valued points. Combined
with function rigidity, vanishing on those points detects a pointed group-valued map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem overHom_fieldPoint_eq_of_field_baseChanges
    {S : Scheme.{u}} {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map g)
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ S) (x : Over.mk s ⟶ X) : x ≫ f = x ≫ g := by
  let l : Spec (.of K) ⟶ pullback X.hom s :=
    pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x)
  have H := congrArg (fun z => l ≫ z.left ≫ pullback.fst Y.hom s) (h K s)
  apply Over.OverMorphism.ext
  change x.left ≫ f.left = x.left ≫ g.left
  simpa only [Over.pullback_map_left, ← Category.assoc, l, pullback.lift_fst] using H

set_option backward.isDefEq.respectTransparency false in
theorem overHom_eq_one_of_fieldPoints
    {S : Scheme.{u}} (X Y : Over S) [GrpObj X] [GrpObj Y] [UniversallyClosed X.hom]
    (hΓ : ∀ V : S.Opens, IsIso (X.hom ∣_ V).appTop)
    (f : X ⟶ Y) (hzero : η[X] ≫ f = η[Y])
    (hfield : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S) (x : Over.mk s ⟶ X), x ≫ f = 1) :
    f = 1 := by
  have hpoint (x : X.left) : f.left x = f.left (η[X].left (X.hom x)) := by
    let a := X.left.fromSpecResidueField x
    let s := a ≫ X.hom
    let a' : Over.mk s ⟶ X := Over.homMk a rfl
    have h := congrArg Over.Hom.left (hfield (X.left.residueField x) s a')
    have hp := congrArg (fun k : Spec (X.left.residueField x) ⟶ Y.left =>
      k (IsLocalRing.closedPoint (X.left.residueField x))) h
    change f.left (a (IsLocalRing.closedPoint (X.left.residueField x))) =
      η[Y].left (s (IsLocalRing.closedPoint (X.left.residueField x))) at hp
    have hx : f.left x = η[Y].left (X.hom x) := by
      simpa only [a, s, Scheme.Hom.comp_apply,
        Scheme.fromSpecResidueField_apply] using hp
    have hz := congrArg (fun k : S ⟶ Y.left => k (X.hom x)) (congrArg Over.Hom.left hzero)
    exact hx.trans hz.symm
  have hσ : η[X].left ≫ X.hom = 𝟙 S := Over.w η[X]
  have h := PointwiseFiberRigidity.Construction.map_eq_of_pointwise_fiber_constancy X.hom hΓ η[X].left hσ f.left hpoint
  apply Over.OverMorphism.ext
  change f.left = X.hom ≫ η[Y].left
  exact h.trans (congrArg (fun k => X.hom ≫ k) (congrArg Over.Hom.left hzero))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PointGroupDetection.Construction
