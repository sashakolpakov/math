import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps.Construction

/-! Pointwise criteria for the subgroup-scheme inclusion in IsogenyQuotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A map preserving the group law on all test-object points is a
homomorphism of group objects. -/
theorem isMonHom_of_pointwise
    {G H : C} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h_one : ∀ X : C, (1 : X ⟶ G) ≫ f = 1)
    (h_mul : ∀ (X : C) (a b : X ⟶ G),
      (a * b) ≫ f = (a ≫ f) * (b ≫ f)) : IsMonHom f := by
  constructor
  · have hunit : toUnit (𝟙_ C) = 𝟙 (𝟙_ C) := toUnit_unique _ _
    simpa only [Hom.one_def, hunit, Category.id_comp] using h_one (𝟙_ C)
  · have h := h_mul (G ⊗ G) (fst G G) (snd G G)
    have hpair : lift (fst G G ≫ f) (snd G G ≫ f) = f ⊗ₘ f := by
      ext <;> simp
    simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, hpair] using h

/-- A natural group map between represented presheaves induces a group
homomorphism on the representing objects, with the prescribed underlying map. -/
theorem represented_group_map_isMonHom
    (F G : Cᵒᵖ ⥤ GrpCat.{v}) {X Y : C}
    (eF : (F ⋙ forget GrpCat).RepresentableBy X)
    (eG : (G ⋙ forget GrpCat).RepresentableBy Y)
    (a : F ⟶ G) (f : X ⟶ Y)
    (h : ∀ (T : C) (x : T ⟶ X),
      eG.homEquiv (x ≫ f) = (a.app (op T)).hom (eF.homEquiv x)) :
    letI := GrpObj.ofRepresentableBy X F eF
    letI := GrpObj.ofRepresentableBy Y G eG
    IsMonHom f := by
  let _ := GrpObj.ofRepresentableBy X F eF
  let _ := GrpObj.ofRepresentableBy Y G eG
  let eX := yonedaGrpObjIsoOfRepresentableBy X F eF
  let eY := yonedaGrpObjIsoOfRepresentableBy Y G eG
  let pointMap (T : C) : (T ⟶ X) →* (T ⟶ Y) :=
    ((eY.inv.app (op T)).hom).comp
      (((a.app (op T)).hom).comp ((eX.hom.app (op T)).hom))
  have hpoint (T : C) (x : T ⟶ X) : pointMap T x = x ≫ f := by
    apply eG.homEquiv.injective
    change eG.homEquiv (eG.homEquiv.symm ((a.app (op T)).hom (eF.homEquiv x))) =
      eG.homEquiv (x ≫ f)
    rw [Equiv.apply_symm_apply, h]
  apply isMonHom_of_pointwise f
  · intro T
    rw [← hpoint]
    exact (pointMap T).map_one
  · intro T x y
    rw [← hpoint, ← hpoint, ← hpoint]
    exact (pointMap T).map_mul x y

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps.Construction
