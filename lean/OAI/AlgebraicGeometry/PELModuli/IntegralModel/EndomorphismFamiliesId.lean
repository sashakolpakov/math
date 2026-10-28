import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import Mathlib.Algebra.Category.Ring.Basic

/-! # Endomorphism Families Id -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismFamiliesId

noncomputable section

/-! The ring-valued functor of actual endomorphisms of the pulled-back
abelian scheme. Restriction is geometric pullback conjugated by the
canonical group-scheme comparisons. Functor laws are proved on the actual
scheme morphisms using their pullback projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ}

def _root_.OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions.GroupEndRing.transport {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : Finite.Actions.GroupEndRing A →+* Finite.Actions.GroupEndRing B where
  toFun f := Finite.Actions.GroupEndRing.ofHom B (e.inv ≫ f.hom A ≫ e.hom)
  map_zero' := by
    apply Finite.Actions.GroupEndRing.ext
    change e.inv ≫ (1 : A.scheme ⟶ A.scheme) ≫ e.hom = 1
    rw [MonObj.one_comp, MonObj.comp_one]
  map_one' := by
    apply Finite.Actions.GroupEndRing.ext
    change e.inv ≫ (𝟙 A.scheme) ≫ e.hom = 𝟙 B.scheme
    simp only [Category.id_comp, e.inv_hom_id]
  map_add' f h := by
    apply Finite.Actions.GroupEndRing.ext
    change e.inv ≫ (f.hom A * h.hom A) ≫ e.hom =
      (e.inv ≫ f.hom A ≫ e.hom) * (e.inv ≫ h.hom A ≫ e.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul]
  map_mul' f h := by
    apply Finite.Actions.GroupEndRing.ext
    change e.inv ≫ (h.hom A ≫ f.hom A) ≫ e.hom =
      (e.inv ≫ h.hom A ≫ e.hom) ≫ (e.inv ≫ f.hom A ≫ e.hom)
    simp only [Category.assoc, e.hom_inv_id_assoc]

namespace EndomorphismFamilies

variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T U V : Over S}

def familyMap (f : T ⟶ U) : pullback A.scheme.hom T.hom ⟶ pullback A.scheme.hom U.hom :=
  pullback.lift (pullback.fst A.scheme.hom T.hom)
    (pullback.snd A.scheme.hom T.hom ≫ f.left) (by
      rw [Category.assoc, f.w, pullback.condition])

@[reassoc (attr := simp)] theorem familyMap_fst (f : T ⟶ U) :
    familyMap A f ≫ pullback.fst A.scheme.hom U.hom =
      pullback.fst A.scheme.hom T.hom := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem familyMap_snd (f : T ⟶ U) :
    familyMap A f ≫ pullback.snd A.scheme.hom U.hom =
      pullback.snd A.scheme.hom T.hom ≫ f.left := pullback.lift_snd _ _ _

@[simp] theorem familyMap_id (T : Over S) : familyMap A (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext
  · exact (familyMap_fst A _).trans (Category.id_comp _).symm
  · exact (familyMap_snd A (𝟙 T)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem familyMap_comp (f : T ⟶ U) (h : U ⟶ V) :
    familyMap A (f ≫ h) = familyMap A f ≫ familyMap A h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familyMap_fst]
  · simp only [Category.assoc, familyMap_snd_assoc, familyMap_snd, Over.comp_left]

def restrictionIso (f : T ⟶ U) :
    ((A.pullback U.hom).pullback f.left).scheme ≅ (A.pullback T.hom).scheme :=
  (A.pullbackCompIso U.hom f.left).symm ≪≫
    A.pullbackCongrIso (f.left ≫ U.hom) T.hom f.w

instance (f : T ⟶ U) : IsMonHom (restrictionIso A f).hom := by
  dsimp only [restrictionIso, Iso.trans_hom]
  infer_instance

theorem restrictionIso_hom_fst (f : T ⟶ U) :
    (restrictionIso A f).hom.left ≫ pullback.fst A.scheme.hom T.hom =
      pullback.fst (A.pullback U.hom).scheme.hom f.left ≫
        pullback.fst A.scheme.hom U.hom := by
  have hcongr (p q : T.left ⟶ S) (w : p = q) :
      (A.pullbackCongrIso p q w).hom.left ≫ pullback.fst A.scheme.hom q =
        pullback.fst A.scheme.hom p := by
    cases w
    exact Category.id_comp _
  change ((A.pullbackCompIso U.hom f.left).inv.left ≫
      (A.pullbackCongrIso (f.left ≫ U.hom) T.hom f.w).hom.left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (A.pullbackCompIso U.hom f.left).inv.left ≫ q)
      (hcongr (f.left ≫ U.hom) T.hom f.w)).trans
      (A.pullbackCompIso_inv_left_fst U.hom f.left))

def schemeRestrictionIso (f : T ⟶ U) :
    pullback (pullback.snd A.scheme.hom U.hom) f.left ≅ pullback A.scheme.hom T.hom :=
  (Over.forget T.left).mapIso (restrictionIso A f)

theorem schemeRestrictionIso_hom_fst (f : T ⟶ U) :
    (schemeRestrictionIso A f).hom ≫ pullback.fst A.scheme.hom T.hom =
      pullback.fst (pullback.snd A.scheme.hom U.hom) f.left ≫
        pullback.fst A.scheme.hom U.hom := restrictionIso_hom_fst A f

theorem restrictionIso_inv_fst (f : T ⟶ U) :
    (schemeRestrictionIso A f).inv ≫ pullback.fst (pullback.snd A.scheme.hom U.hom) f.left =
      familyMap A f := by
  apply pullback.hom_ext
  · rw [Category.assoc, ← schemeRestrictionIso_hom_fst, ← Category.assoc,
      (schemeRestrictionIso A f).inv_hom_id, Category.id_comp, familyMap_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h : (schemeRestrictionIso A f).inv ≫
        pullback.snd (pullback.snd A.scheme.hom U.hom) f.left =
          pullback.snd A.scheme.hom T.hom := (restrictionIso A f).inv.w
    rw [h, familyMap_snd]

def restrict (f : T ⟶ U) : Finite.Actions.GroupEndRing (A.pullback U.hom) →+* Finite.Actions.GroupEndRing (A.pullback T.hom) :=
  (Finite.Actions.GroupEndRing.transport (restrictionIso A f)).comp
    (Finite.Actions.GroupEndRing.pullback (A.pullback U.hom) f.left)

def endHom {T : Over S} (r : Finite.Actions.GroupEndRing (A.pullback T.hom)) :
    pullback A.scheme.hom T.hom ⟶ pullback A.scheme.hom T.hom :=
  (r.hom (A.pullback T.hom)).left

/-- The defining restriction formula is an equality of actual scheme maps. -/
theorem restrict_fst (f : T ⟶ U) (r : Finite.Actions.GroupEndRing (A.pullback U.hom)) :
    endHom A (restrict A f r) ≫ pullback.fst A.scheme.hom T.hom =
      familyMap A f ≫ endHom A r ≫ pullback.fst A.scheme.hom U.hom := by
  let m : pullback (pullback.snd A.scheme.hom U.hom) f.left ⟶
      pullback (pullback.snd A.scheme.hom U.hom) f.left :=
    ((Over.pullback f.left).map (r.hom (A.pullback U.hom))).left
  have hm : m ≫ pullback.fst (pullback.snd A.scheme.hom U.hom) f.left =
      pullback.fst (pullback.snd A.scheme.hom U.hom) f.left ≫ endHom A r :=
    AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst _ _
  change ((schemeRestrictionIso A f).inv ≫ m ≫ (schemeRestrictionIso A f).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, schemeRestrictionIso_hom_fst,
    ← Category.assoc m, hm, ← Category.assoc,
    ← Category.assoc (schemeRestrictionIso A f).inv _ (endHom A r),
    restrictionIso_inv_fst, Category.assoc]

theorem ext_of_fst {r q : Finite.Actions.GroupEndRing (A.pullback T.hom)}
    (h : endHom A r ≫ pullback.fst A.scheme.hom T.hom =
      endHom A q ≫ pullback.fst A.scheme.hom T.hom) : r = q := by
  apply Finite.Actions.GroupEndRing.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (r.hom (A.pullback T.hom)).w.trans (q.hom (A.pullback T.hom)).w.symm

theorem restrict_id (T : Over S) (r : Finite.Actions.GroupEndRing (A.pullback T.hom)) :
    restrict A (𝟙 T) r = r := by
  apply ext_of_fst A
  rw [restrict_fst, familyMap_id, Category.id_comp]

theorem restrict_comp (f : T ⟶ U) (h : U ⟶ V) (r : Finite.Actions.GroupEndRing (A.pullback V.hom)) :
    restrict A (f ≫ h) r = restrict A f (restrict A h r) := by
  apply ext_of_fst A
  rw [restrict_fst, restrict_fst, restrict_fst, familyMap_comp, Category.assoc]

/-- The genuine ring-valued endomorphism functor on all test schemes. -/
def endomorphismFunctor : (Over S)ᵒᵖ ⥤ RingCat.{u} where
  obj T := RingCat.of (Finite.Actions.GroupEndRing (A.pullback T.unop.hom))
  map f := RingCat.ofHom (restrict A f.unop)
  map_id T := by
    apply RingCat.hom_ext
    exact RingHom.ext (restrict_id A T.unop)
  map_comp f h := by
    apply RingCat.hom_ext
    exact RingHom.ext (restrict_comp A h.unop f.unop)

end EndomorphismFamilies

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismFamiliesId
