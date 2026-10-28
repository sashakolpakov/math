import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftTranslation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionLiftFibers

/-! # Group Lift Open Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftOpenCoordinates

noncomputable section

section

/-! Lifts of a group-valued map through a surjective thickening are
actual lifts into any open chart of the identity, after translation.
The original map is recovered by multiplication with its reference. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme} {S T U A : Over B} [GrpObj A]
    (r : S ⟶ T) [Surjective r.left] (i : U ⟶ A) [IsOpenImmersion i.left]
    (x : S ⟶ U) (hx : x ≫ i = 1) (c : T ⟶ A)

def groupLiftOpenEquiv : {f : T ⟶ A // r ≫ f = r ≫ c} ≃ {f : T ⟶ U // r ≫ f = x} :=
  (GroupLiftTranslation.groupLiftIdentityEquiv r c).trans
    ((Equiv.subtypeEquivRight (fun f : T ⟶ A =>
      show (r ≫ f = 1) ↔ (r ≫ f = x ≫ i) by rw [hx])).trans
        (Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv r i x).symm)

theorem groupLiftOpenEquiv_fac (f : {f : T ⟶ A // r ≫ f = r ≫ c}) :
    (groupLiftOpenEquiv r i x hx c f).val ≫ i = f.val / c :=
  DualOpen.Lifts.overOpenLift_fac i (f.val / c) _

theorem groupLiftOpenEquiv_recovery (f : {f : T ⟶ A // r ≫ f = r ≫ c}) :
    ((groupLiftOpenEquiv r i x hx c f).val ≫ i) * c = f.val := by
  rw [groupLiftOpenEquiv_fac]
  exact div_mul_cancel _ _

end

/-! The actual translated lift into an identity neighborhood commutes
with restriction of its coefficient test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme} {S T S' T' U A : Over B} [GrpObj A]
    (r : S ⟶ T) [Surjective r.left] (r' : S' ⟶ T') [Surjective r'.left]
    (a : S' ⟶ S) (b : T' ⟶ T) (h : r' ≫ b = a ≫ r)
    (i : U ⟶ A) [IsOpenImmersion i.left] (x : S ⟶ U) (hx : x ≫ i = 1) (c : T ⟶ A)

def groupLiftRestricted (f : {f : T ⟶ A // r ≫ f = r ≫ c}) :
    {f : T' ⟶ A // r' ≫ f = r' ≫ (b ≫ c)} :=
  ⟨b ≫ f.val, by
    calc
      r' ≫ (b ≫ f.val) = a ≫ (r ≫ f.val) := by rw [← Category.assoc, h, Category.assoc]
      _ = a ≫ (r ≫ c) := congrArg (fun z => a ≫ z) f.property
      _ = r' ≫ (b ≫ c) := by rw [← Category.assoc, ← h, Category.assoc]⟩

theorem groupLiftOpenEquiv_natural (f : {f : T ⟶ A // r ≫ f = r ≫ c}) :
    b ≫ (groupLiftOpenEquiv r i x hx c f).val =
      (groupLiftOpenEquiv r' i (a ≫ x) (by rw [Category.assoc, hx, MonObj.comp_one]) (b ≫ c)
        (groupLiftRestricted r r' a b h c f)).val := by
  have : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  rw [Category.assoc, groupLiftOpenEquiv_fac, groupLiftOpenEquiv_fac, GrpObj.comp_div]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftOpenCoordinates
