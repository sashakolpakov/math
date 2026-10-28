import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupLocus
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-! # Relative Point Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Convert TorsionQuotient's actual relative subgroup over the base into the TateComparison
point-subgroup interface. The finite etale group structure is constructed
on its representing scheme from the genuine subgroup presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def RelativePointSubgroups.testToBase (T : Over S) : T ⟶ Over.mk (𝟙 S) :=
  Over.homMk T.hom (Category.comp_id _)

theorem RelativePointSubgroups.testToBase_unique (T : Over S) (t : T ⟶ Over.mk (𝟙 S)) : t = RelativePointSubgroups.testToBase T := by
  apply Over.OverMorphism.ext
  change t.left = T.hom
  have h := t.w
  change t.left ≫ 𝟙 S = T.hom at h
  exact (Category.comp_id t.left).symm.trans h

def RelativePointSubgroups.relativeToPointSubgroup (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))) : Subgroups.PointSubgroup A where
  atTest T := F.points T (RelativePointSubgroups.testToBase T)
  pullback_mem {T U} f x hx := by
    have h := F.naturality f (RelativePointSubgroups.testToBase U) hx
    rwa [RelativePointSubgroups.testToBase_unique T (f ≫ RelativePointSubgroups.testToBase U)] at h

def RelativePointSubgroups.pointToRelativeSubgroup (F : Subgroups.PointSubgroup A) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S)) where
  points T _ := F.atTest T
  naturality := by
    intro T U f t x hx
    exact F.pullback_mem f x hx

theorem RelativePointSubgroups.relativeToPoint_pointToRelative (F : Subgroups.PointSubgroup A) :
    RelativePointSubgroups.relativeToPointSubgroup A (RelativePointSubgroups.pointToRelativeSubgroup A F) = F := by
  apply Subgroups.PointSubgroup.ext
  intro T
  rfl

theorem RelativePointSubgroups.pointToRelative_relativeToPoint (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))) :
    RelativePointSubgroups.pointToRelativeSubgroup A (RelativePointSubgroups.relativeToPointSubgroup A F) = F := by
  ext T t x
  change x ∈ F.points T (RelativePointSubgroups.testToBase T) ↔ x ∈ F.points T t
  rw [RelativePointSubgroups.testToBase_unique T t]

theorem RelativePointSubgroups.pointToRelative_hasModel (F : Subgroups.PointSubgroup A) (hF : F.HasFiniteEtaleModel) :
    Nonempty (RelativePointSubgroups.pointToRelativeSubgroup A F).Model := by
  obtain ⟨H, i, _, hi, hf, he, hpoints⟩ := hF
  have : Mono i := hi
  have : Etale H.X.hom := he
  refine ⟨{
    carrier := H.X
    toBase := RelativePointSubgroups.testToBase H.X
    toGroup := i
    finite := hf
    flat := inferInstanceAs (Flat H.X.hom)
    finitePresentation := inferInstanceAs (LocallyOfFinitePresentation H.X.hom)
    jointly_monic := fun _ _ _ _ hab => (cancel_mono i).mp hab
    points_iff := ?_ }⟩
  intro T t x
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := (hpoints T x).mp hx
    exact ⟨f, (RelativePointSubgroups.testToBase_unique T _).trans (RelativePointSubgroups.testToBase_unique T t).symm, hf⟩
  · rintro ⟨f, _, hf⟩
    exact (hpoints T x).mpr ⟨f, hf⟩

section

variable {A}

def Subgroups.PointSubgroup.pointGroups (F : Subgroups.PointSubgroup A) : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (F.atTest T.unop)
  map f := CommGrpCat.ofHom {
    toFun x := ⟨f.unop ≫ x.val, F.pullback_mem f.unop x.val x.property⟩
    map_one' := Subtype.ext (MonObj.comp_one _)
    map_mul' x y := Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.id_comp x.val)
  map_comp f h := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc _ _ _)

end

variable (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))) (R : F.Model)

def RelativePointSubgroups.relativeToPointRepresentable :
    ((RelativePointSubgroups.relativeToPointSubgroup A F).pointGroups ⋙ forget CommGrpCat).RepresentableBy R.carrier := by
  let toPoint {T : Over S} (f : T ⟶ R.carrier) : (RelativePointSubgroups.relativeToPointSubgroup A F).atTest T :=
    ⟨f ≫ R.toGroup, (R.points_iff T (RelativePointSubgroups.testToBase T) _).mpr
      ⟨f, RelativePointSubgroups.testToBase_unique T (f ≫ R.toBase), rfl⟩⟩
  have hinj (T : Over S) : Function.Injective (@toPoint T) := by
    intro f h he
    apply R.jointly_monic T f h
    · exact (RelativePointSubgroups.testToBase_unique T _).trans (RelativePointSubgroups.testToBase_unique T _).symm
    · exact congrArg Subtype.val he
  have hsurj (T : Over S) : Function.Surjective (@toPoint T) := by
    intro x
    obtain ⟨f, _, hf⟩ := (R.points_iff T (RelativePointSubgroups.testToBase T) x.val).mp x.property
    exact ⟨f, Subtype.ext hf⟩
  exact {
    homEquiv := Equiv.ofBijective toPoint ⟨hinj _, hsurj _⟩
    homEquiv_comp f h := Subtype.ext (Category.assoc _ _ _) }

def RelativePointSubgroups.relativeToPointGroup : CommGrp (Over S) := by
  letI := CommGrpObj.ofRepresentableBy R.carrier (RelativePointSubgroups.relativeToPointSubgroup A F).pointGroups
    (RelativePointSubgroups.relativeToPointRepresentable A F R)
  exact CommGrp.mk R.carrier

theorem RelativePointSubgroups.relativeToPointInclusion_isMonHom :
    letI : GrpObj R.carrier := (RelativePointSubgroups.relativeToPointGroup A F R).grp
    IsMonHom R.toGroup := by
  let : GrpObj R.carrier := (RelativePointSubgroups.relativeToPointGroup A F R).grp
  let e := yonedaGrpObjIsoOfRepresentableBy R.carrier
    ((RelativePointSubgroups.relativeToPointSubgroup A F).pointGroups ⋙ forget₂ CommGrpCat GrpCat)
    (RelativePointSubgroups.relativeToPointRepresentable A F R)
  let pointMap (T : Over S) : (T ⟶ R.carrier) →* (T ⟶ A.scheme) :=
    ((RelativePointSubgroups.relativeToPointSubgroup A F).atTest T).subtype.comp ((e.hom.app (op T)).hom)
  have hpoint (T : Over S) (x : T ⟶ R.carrier) : pointMap T x = x ≫ R.toGroup := rfl
  apply IsogenyQuotient.GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    rw [← hpoint]
    exact (pointMap T).map_one
  · intro T x y
    rw [← hpoint, ← hpoint, ← hpoint]
    exact (pointMap T).map_mul x y

include R in
theorem RelativePointSubgroups.relativeToPoint_hasFiniteEtaleModel (n : ℕ) (hk : F.KilledBy n)
    (ht : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme n).hom) :
    (RelativePointSubgroups.relativeToPointSubgroup A F).HasFiniteEtaleModel := by
  let G := RelativePointSubgroups.relativeToPointGroup A F R
  let : GrpObj R.carrier := G.grp
  have hi : IsMonHom R.toGroup := RelativePointSubgroups.relativeToPointInclusion_isMonHom A F R
  have hm : Mono R.toGroup := by
    constructor
    intro T f h he
    exact R.jointly_monic T f h
      ((RelativePointSubgroups.testToBase_unique T _).trans (RelativePointSubgroups.testToBase_unique T _).symm) he
  have hstruct : R.toBase.left = R.carrier.hom := by
    have h := R.toBase.w
    change R.toBase.left ≫ 𝟙 S = R.carrier.hom at h
    exact (Category.comp_id R.toBase.left).symm.trans h
  have hf : IsFinite R.carrier.hom := hstruct ▸ R.finite
  have he : Etale R.carrier.hom := hstruct ▸ IsogenyQuotient.SubgroupLocus.Construction.subgroup_model_etale F R n hk ht
  refine ⟨G, R.toGroup, hi, hm, hf, he, ?_⟩
  intro T x
  exact ⟨fun hx => (R.points_iff T (RelativePointSubgroups.testToBase T) x).mp hx |>.imp
    (fun _ hf => hf.2), fun ⟨f, hf⟩ => (R.points_iff T (RelativePointSubgroups.testToBase T) x).mpr
      ⟨f, RelativePointSubgroups.testToBase_unique T _, hf⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
