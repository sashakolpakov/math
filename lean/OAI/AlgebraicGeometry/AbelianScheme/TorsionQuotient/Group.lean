import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group.TorsionGroup

/-!
# TorsionQuotient: the group structure on the actual torsion equalizer

The group-valued torsion functor is constructed first and represented by
the existing equalizer. Its group law and inclusion are then recovered
from that representation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)

def points (T : Over S) : Subgroup (T ⟶ A) where
  carrier := {a | a ^ n = 1}
  one_mem' := one_pow n
  mul_mem' := by intro a b ha hb; change (a * b) ^ n = 1; rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by intro a ha; change a⁻¹ ^ n = 1; rw [inv_pow, ha, inv_one]

noncomputable def pointFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (points A n T.unop)
  map f := GrpCat.ofHom
    { toFun := fun a => ⟨f.unop ≫ a.val, by
        change (f.unop ≫ a.val) ^ n = 1
        rw [← MonObj.comp_pow, a.property, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' a b := Subtype.ext (MonObj.comp_mul _ a.val b.val) }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact Subtype.ext (Category.id_comp a.val)
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact Subtype.ext (Category.assoc g.unop f.unop a.val)

noncomputable def pointsEquiv (T : Over S) : (T ⟶ SubgroupFunctor.torsionScheme A n) ≃ points A n T where
  toFun a := ⟨a ≫ SubgroupFunctor.torsionι A n,
    (SubgroupFunctor.factors_through_torsion_iff n (a ≫ SubgroupFunctor.torsionι A n)).mp ⟨a, rfl⟩⟩
  invFun a := SubgroupFunctor.torsionLift n a.val a.property
  left_inv a := by
    apply equalizer.hom_ext
    exact SubgroupFunctor.torsionLift_ι n (a ≫ SubgroupFunctor.torsionι A n) _
  right_inv a := Subtype.ext (SubgroupFunctor.torsionLift_ι n a.val a.property)

noncomputable def representable :
    (pointFunctor A n ⋙ forget GrpCat).RepresentableBy (SubgroupFunctor.torsionScheme A n) where
  homEquiv := pointsEquiv A n _
  homEquiv_comp f a := Subtype.ext (Category.assoc f a (SubgroupFunctor.torsionι A n))

noncomputable instance group : GrpObj (SubgroupFunctor.torsionScheme A n) :=
  GrpObj.ofRepresentableBy _ (pointFunctor A n) (representable A n)

noncomputable def pointIso : yonedaGrpObj (SubgroupFunctor.torsionScheme A n) ≅ pointFunctor A n :=
  yonedaGrpObjIsoOfRepresentableBy _ (pointFunctor A n) (representable A n)

theorem pointsEquiv_one (T : Over S) : pointsEquiv A n T 1 = 1 :=
  ((pointIso A n).hom.app (.op T)).hom.map_one

theorem pointsEquiv_mul (T : Over S) (a b : T ⟶ SubgroupFunctor.torsionScheme A n) :
    pointsEquiv A n T (a * b) = pointsEquiv A n T a * pointsEquiv A n T b :=
  ((pointIso A n).hom.app (.op T)).hom.map_mul a b

instance commutative : IsCommMonObj (SubgroupFunctor.torsionScheme A n) := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (pointsEquiv A n T).injective
  rw [pointsEquiv_mul, pointsEquiv_mul, mul_comm]

instance inclusion_isMonHom : IsMonHom (SubgroupFunctor.torsionι A n) where
  one_hom := by
    have h := congrArg Subtype.val (pointsEquiv_one A n (𝟙_ (Over S)))
    change (1 : 𝟙_ (Over S) ⟶ SubgroupFunctor.torsionScheme A n) ≫ SubgroupFunctor.torsionι A n = (1 : 𝟙_ (Over S) ⟶ A) at h
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h
  mul_hom := by
    let K := SubgroupFunctor.torsionScheme A n
    have h := congrArg Subtype.val (pointsEquiv_mul A n (K ⊗ K) (fst K K) (snd K K))
    change (fst K K * snd K K) ≫ SubgroupFunctor.torsionι A n =
      (fst K K ≫ SubgroupFunctor.torsionι A n) * (snd K K ≫ SubgroupFunctor.torsionι A n) at h
    have hp : lift (fst K K ≫ SubgroupFunctor.torsionι A n) (snd K K ≫ SubgroupFunctor.torsionι A n) =
        SubgroupFunctor.torsionι A n ⊗ₘ SubgroupFunctor.torsionι A n := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (lift_fst _ _).trans (tensorHom_fst _ _).symm
      · exact (lift_snd _ _).trans (tensorHom_snd _ _).symm
    exact (congrArg (fun a => a ≫ SubgroupFunctor.torsionι A n) (MonObj.mul_eq_mul (M := K))).trans
      (h.trans (congrArg (fun a => a ≫ μ[A]) hp))

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group.TorsionGroup
