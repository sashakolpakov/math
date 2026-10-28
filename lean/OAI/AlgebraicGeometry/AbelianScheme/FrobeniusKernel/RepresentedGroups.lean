import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Represented Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedGroups.Construction

noncomputable section

/-!
Represent a group-valued functor whose values may be larger than the hom
universe. The group law and maps are recovered from the functor; the point
comparison is proved multiplicative, rather than supplied as an input.
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj IsMulCommutative

universe u v w

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def representedGroup (F : Cᵒᵖ ⥤ GrpCat.{w}) (X : C)
    (r : (F ⋙ forget GrpCat).RepresentableBy X) : Grp C :=
  @Grp.mk C _ _ X (GrpObj.ofRepresentableBy X F r)

def representedGroupPoints (F : Cᵒᵖ ⥤ GrpCat.{w}) (X : C)
    (r : (F ⋙ forget GrpCat).RepresentableBy X) (T : C) :
    (T ⟶ (representedGroup F X r).X) ≃* F.obj (op T) where
  toEquiv := r.homEquiv
  map_mul' a b := by
    change T ⟶ X at a b
    change r.homEquiv (lift a b ≫ r.homEquiv.symm
      (r.homEquiv (fst X X) * r.homEquiv (snd X X))) = r.homEquiv a * r.homEquiv b
    rw [r.homEquiv_comp, Equiv.apply_symm_apply]
    change (F.map (lift a b).op) (r.homEquiv (fst X X) * r.homEquiv (snd X X)) = _
    rw [map_mul]
    exact congrArg₂ (· * ·)
      ((r.homEquiv_comp (lift a b) (fst X X)).symm.trans
        (congrArg r.homEquiv (lift_fst a b)))
      ((r.homEquiv_comp (lift a b) (snd X X)).symm.trans
        (congrArg r.homEquiv (lift_snd a b)))

theorem representedGroup_commutative [BraidedCategory C]
    (F : Cᵒᵖ ⥤ GrpCat.{w}) [∀ T, IsMulCommutative (F.obj T)] (X : C)
    (r : (F ⋙ forget GrpCat).RepresentableBy X) :
    IsCommMonObj (representedGroup F X r).X := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (representedGroupPoints F X r T).injective
  rw [map_mul, map_mul, mul_comm]

theorem isMonHom_of_point_operations {X Y : C} [GrpObj X] [GrpObj Y]
    (f : X ⟶ Y)
    (h₁ : ∀ T, (1 : T ⟶ X) ≫ f = 1)
    (hmul : ∀ T (a b : T ⟶ X), (a * b) ≫ f = (a ≫ f) * (b ≫ f)) : IsMonHom f where
  one_hom := by
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h₁ (𝟙_ C)
  mul_hom := by
    have hp : lift (fst X X ≫ f) (snd X X ≫ f) = f ⊗ₘ f := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (lift_fst _ _).trans (tensorHom_fst _ _).symm
      · exact (lift_snd _ _).trans (tensorHom_snd _ _).symm
    exact (congrArg (fun a => a ≫ f) (MonObj.mul_eq_mul (M := X))).trans
      ((hmul (X ⊗ X) (fst X X) (snd X X)).trans
        (congrArg (fun a => a ≫ μ[Y]) hp))

variable {F G : Cᵒᵖ ⥤ GrpCat.{w}} {X Y : C}
variable (rF : (F ⋙ forget GrpCat).RepresentableBy X)
variable (rG : (G ⋙ forget GrpCat).RepresentableBy Y)

def representedGroupMap (f : F ⟶ G) :
    X ⟶ Y :=
  rG.homEquiv.symm (f.app (op X) (rF.homEquiv (𝟙 X)))

omit [CartesianMonoidalCategory C] in
theorem representedGroupMap_action (f : F ⟶ G) {T : C} (a : T ⟶ X) :
    rG.homEquiv (a ≫ representedGroupMap rF rG f) = f.app (op T) (rF.homEquiv a) := by
  rw [rG.homEquiv_comp]
  dsimp only [representedGroupMap]
  rw [Equiv.apply_symm_apply]
  have h := f.naturality_apply a.op (rF.homEquiv (𝟙 X))
  exact h.symm.trans (congrArg (fun x => f.app (op T) x)
    ((rF.homEquiv_comp a (𝟙 X)).symm.trans
      (congrArg rF.homEquiv (Category.comp_id a))))

instance representedGroupMap_isMonHom (f : F ⟶ G) :
    letI := GrpObj.ofRepresentableBy X F rF
    letI := GrpObj.ofRepresentableBy Y G rG
    IsMonHom (representedGroupMap rF rG f) := by
  let := GrpObj.ofRepresentableBy X F rF
  let := GrpObj.ofRepresentableBy Y G rG
  apply isMonHom_of_point_operations
  · intro T
    apply rG.homEquiv.injective
    rw [representedGroupMap_action]
    exact (congrArg (fun x => f.app (op T) x) (representedGroupPoints F X rF T).map_one).trans
      (((f.app (op T)).hom.map_one).trans (representedGroupPoints G Y rG T).map_one.symm)
  · intro T a b
    apply rG.homEquiv.injective
    rw [representedGroupMap_action]
    exact (congrArg (fun x => f.app (op T) x)
      ((representedGroupPoints F X rF T).map_mul a b)).trans
        (((f.app (op T)).hom.map_mul _ _).trans
          ((congrArg₂ (· * ·) (representedGroupMap_action rF rG f a).symm
            (representedGroupMap_action rF rG f b).symm).trans
              ((representedGroupPoints G Y rG T).map_mul _ _).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedGroups.Construction
