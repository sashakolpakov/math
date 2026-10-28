import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.Subobject.Basic

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

noncomputable section

/-!
# Scheme-theoretic kernels for PoincareBundle

The kernel is the fiber product over the identity section. Its universal
property identifies its points over every test object with the group
kernel, so infinitesimal points are retained.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- Postcomposition with a group-object morphism on all test objects. -/
def pointsMap (T : C) : (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := MonObj.one_comp f
  map_mul' x y := MonObj.mul_comp x y f

/-- The scheme-theoretic kernel object, defined as a fiber product. -/
abbrev kernelObject : C := pullback f η[B]

/-- The kernel inclusion. -/
def kernelInclusion : kernelObject f ⟶ A := pullback.fst f η[B]

instance : Mono (kernelInclusion f) := by
  have : Mono η[B] := ⟨fun _ _ _ => Subsingleton.elim _ _⟩
  constructor
  intro T x y h
  apply pullback.hom_ext
  · exact h
  · exact Subsingleton.elim _ _

/-- Its test-object points are exactly the kernel of postcomposition. -/
def kernelPointsEquiv (T : C) :
    (T ⟶ kernelObject f) ≃ (pointsMap f T).ker where
  toFun x := ⟨x ≫ kernelInclusion f, by
    change (x ≫ kernelInclusion f) ≫ f = 1
    rw [Category.assoc, kernelInclusion, pullback.condition]
    rw [← Category.assoc]
    change (x ≫ pullback.snd f η[B]) ≫ η[B] = toUnit T ≫ η[B]
    rw [Subsingleton.elim (x ≫ pullback.snd f η[B]) (toUnit T)]⟩
  invFun x := pullback.lift x.1 (toUnit T) x.2
  left_inv x := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · apply Subsingleton.elim
  right_inv x := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

/-- Kernel points form a presheaf of groups. -/
def kernelPointFunctor : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (pointsMap f T.unop).ker
  map {T U} a := GrpCat.ofHom {
    toFun x := ⟨a.unop ≫ x.1, by
      change (a.unop ≫ x.1) ≫ f = 1
      rw [Category.assoc, show x.1 ≫ f = 1 from x.2, MonObj.comp_one]⟩
    map_one' := by
      apply Subtype.ext
      exact MonObj.comp_one a.unop
    map_mul' x y := by
      apply Subtype.ext
      exact MonObj.comp_mul a.unop x.1 y.1 }
  map_id T := by
    ext x
    exact Category.id_comp x.1
  map_comp a b := by
    ext x
    exact Category.assoc b.unop a.unop x.1

/-- The fiber product represents the full group-valued kernel presheaf. -/
def kernelRepresentableBy :
    (kernelPointFunctor f ⋙ forget GrpCat).RepresentableBy (kernelObject f) where
  homEquiv := kernelPointsEquiv f _
  homEquiv_comp a x := by
    apply Subtype.ext
    exact Category.assoc a x (kernelInclusion f)

/-- The group structure on the scheme-theoretic kernel is constructed
from its represented group-valued functor. -/
@[instance_reducible]
def kernelGroup : GrpObj (kernelObject f) :=
  GrpObj.ofRepresentableBy _ (kernelPointFunctor f) (kernelRepresentableBy f)

attribute [local instance] kernelGroup

/-- The represented point identification respects the group operations. -/
def kernelPointsMulEquiv (T : C) :
    (T ⟶ kernelObject f) ≃* (pointsMap f T).ker :=
  ((yonedaGrpObjIsoOfRepresentableBy _ (kernelPointFunctor f)
    (kernelRepresentableBy f)).app (op T)).groupIsoToMulEquiv

/-- Inclusion of the kernel as a natural transformation of group presheaves. -/
def kernelPointInclusion : kernelPointFunctor f ⟶ yonedaGrpObj A where
  app T := GrpCat.ofHom (pointsMap f T.unop).ker.subtype
  naturality _ _ a := by
    ext x
    rfl

/-- The kernel inclusion constructed as a morphism of group objects. -/
def kernelInclusionAsGroup : Grp.mk (kernelObject f) ⟶ Grp.mk A :=
  yonedaGrpFullyFaithful.preimage
    ((yonedaGrpObjIsoOfRepresentableBy _ (kernelPointFunctor f)
      (kernelRepresentableBy f)).hom ≫ kernelPointInclusion f)

theorem kernelInclusionAsGroup_hom : (kernelInclusionAsGroup f).hom.hom = kernelInclusion f := by
  change (𝟙 (kernelObject f)) ≫ kernelInclusion f = kernelInclusion f
  exact Category.id_comp _

instance kernelInclusion_isMonHom : IsMonHom (kernelInclusion f) := by
  rw [← kernelInclusionAsGroup_hom f]
  infer_instance

/-- Kernels of morphisms between commutative group objects are commutative. -/
theorem kernelGroup_commutative [BraidedCategory C] [IsCommMonObj A] : IsCommMonObj (kernelObject f) := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (kernelPointsMulEquiv f T).injective
  rw [map_mul, map_mul, mul_comm]

/-- The defining kernel inclusion is annihilated by the original map. -/
theorem kernelInclusion_comp : kernelInclusion f ≫ f = 1 := by
  have h := (kernelPointsEquiv f (kernelObject f) (𝟙 _)).property
  change ((𝟙 (kernelObject f)) ≫ kernelInclusion f) ≫ f = 1 at h
  simpa only [Category.id_comp] using h

/-- A scheme-theoretic kernel as an actual subobject of its source. -/
def kernelSubobject : Subobject A := Subobject.mk (kernelInclusion f)

variable {D : C} [GrpObj D] (g : A ⟶ D) [IsMonHom g]

/-- Containment of kernels can be checked on all test objects. -/
theorem kernelSubobject_le_iff : kernelSubobject f ≤ kernelSubobject g ↔
    ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1 := by
  constructor
  · intro h T x hx
    let i := Subobject.ofMkLEMk (kernelInclusion f) (kernelInclusion g) h
    let y := (kernelPointsEquiv f T).symm ⟨x, hx⟩
    have hy : y ≫ kernelInclusion f = x := pullback.lift_fst _ _ _
    rw [← hy, ← Subobject.ofMkLEMk_comp h, Category.assoc, Category.assoc,
      kernelInclusion_comp g, MonObj.comp_one, MonObj.comp_one]
  · intro h
    let i := (kernelPointsEquiv g (kernelObject f)).symm
      ⟨kernelInclusion f, h _ _ (kernelInclusion_comp f)⟩
    exact Subobject.mk_le_mk_of_comm i (pullback.lift_fst _ _ _)

end

variable {S : Scheme.{u}} {A B : Over S} [GrpObj B] (f : A ⟶ B)

/-- The kernel square remains a pullback after forgetting to schemes. -/
theorem kernel_isPullback :
    IsPullback (kernelInclusion f).left (pullback.snd f η[B]).left f.left η[B].left :=
  (Over.forget S).map_isPullback (IsPullback.of_hasPullback f η[B])

/-- The structural map of the kernel is the second fiber-product projection. -/
theorem kernel_hom_eq_snd : (kernelObject f).hom = (pullback.snd f η[B]).left := by
  simpa using (Over.w (pullback.snd f η[B])).symm

/-- The scheme-theoretic kernel of a finite homomorphism is finite over the base. -/
theorem kernel_isFinite [IsFinite f.left] : IsFinite (kernelObject f).hom := by
  rw [kernel_hom_eq_snd f]
  exact MorphismProperty.of_isPullback (P := @IsFinite) (kernel_isPullback f) inferInstance

/-- The scheme-theoretic kernel of a flat homomorphism is flat over the base. -/
theorem kernel_flat [Flat f.left] : Flat (kernelObject f).hom := by
  rw [kernel_hom_eq_snd f]
  exact MorphismProperty.of_isPullback (P := @Flat) (kernel_isPullback f) inferInstance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
