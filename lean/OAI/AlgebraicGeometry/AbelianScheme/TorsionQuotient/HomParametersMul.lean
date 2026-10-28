import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleLift
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Hom Parameters Mul -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.HomParametersMul.HomParameters

/-!
# TorsionQuotient: the finite etale scheme of homomorphisms from a fixed finite group

An actual finite product supplies one section per group element. A finite
equalizer imposes the unit and multiplication equations. The resulting
scheme represents the group-homomorphism functor on every test scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {S : Scheme.{u}} (H : Over S) [GrpObj H]
variable (M : Type u) [Group M] [Fintype M]

noncomputable abbrev tuples (I : Type u) [Fintype I] : Over S := piObj (fun _ : I => H)

noncomputable abbrev evaluation (i : M) : tuples H M ⟶ H := Pi.π _ i

abbrev RelationIndex := Option (M × M)

noncomputable def relationsLeft : tuples H M ⟶ tuples H (RelationIndex M) := Pi.lift fun i =>
  match i with
  | none => evaluation H M 1
  | some (a, b) => evaluation H M a * evaluation H M b

noncomputable def relationsRight : tuples H M ⟶ tuples H (RelationIndex M) := Pi.lift fun i =>
  match i with
  | none => 1
  | some (a, b) => evaluation H M (a * b)

noncomputable def parameter : Over S := equalizer (relationsLeft H M) (relationsRight H M)

noncomputable def inclusion : parameter H M ⟶ tuples H M :=
  equalizer.ι (relationsLeft H M) (relationsRight H M)

noncomputable def coefficient (m : M) : parameter H M ⟶ H := inclusion H M ≫ evaluation H M m

theorem relation_left_projection (i : RelationIndex M) :
    relationsLeft H M ≫ Pi.π _ i =
      match i with
      | none => evaluation H M 1
      | some (a, b) => evaluation H M a * evaluation H M b := Pi.lift_comp_π _ i

theorem relation_right_projection (i : RelationIndex M) :
    relationsRight H M ≫ Pi.π _ i =
      match i with
      | none => 1
      | some (a, b) => evaluation H M (a * b) := Pi.lift_comp_π _ i

theorem coefficient_relation (i : RelationIndex M) :
    inclusion H M ≫ (match i with
      | none => evaluation H M 1
      | some (a, b) => evaluation H M a * evaluation H M b) =
    inclusion H M ≫ (match i with
      | none => 1
      | some (a, b) => evaluation H M (a * b)) := by
  have h := congrArg (fun z : parameter H M ⟶ tuples H (RelationIndex M) => z ≫ Pi.π _ i)
    (equalizer.condition (relationsLeft H M) (relationsRight H M))
  have hl := (Category.assoc (inclusion H M) (relationsLeft H M) (Pi.π _ i)).trans
    (congrArg (fun z => inclusion H M ≫ z) (relation_left_projection H M i))
  have hr := (Category.assoc (inclusion H M) (relationsRight H M) (Pi.π _ i)).trans
    (congrArg (fun z => inclusion H M ≫ z) (relation_right_projection H M i))
  exact hl.symm.trans (h.trans hr)

theorem coefficient_one : coefficient H M 1 = 1 :=
  (coefficient_relation H M none).trans (MonObj.comp_one _)

theorem coefficient_mul (a b : M) : coefficient H M (a * b) = coefficient H M a * coefficient H M b := by
  exact (coefficient_relation H M (some (a, b))).symm.trans (MonObj.comp_mul _ _ _)

noncomputable def points (T : Over S) (f : T ⟶ parameter H M) : M →* (T ⟶ H) where
  toFun m := f ≫ coefficient H M m
  map_one' := by rw [coefficient_one, MonObj.comp_one]
  map_mul' a b := by rw [coefficient_mul, MonObj.comp_mul]

noncomputable def fromPoints {T : Over S} (a : M →* (T ⟶ H)) : T ⟶ parameter H M :=
  equalizer.lift (Pi.lift a) (by
    apply Pi.hom_ext
    intro i
    cases i with
    | none =>
      simpa only [Category.assoc, relationsLeft, relationsRight, Pi.lift_comp_π,
        evaluation, MonObj.comp_one] using a.map_one
    | some i =>
      rcases i with ⟨x, y⟩
      simpa only [Category.assoc, relationsLeft, relationsRight, Pi.lift_comp_π,
        evaluation, MonObj.comp_mul] using (a.map_mul x y).symm)

@[simp] theorem fromPoints_coefficient {T : Over S} (a : M →* (T ⟶ H)) (m : M) :
    fromPoints H M a ≫ coefficient H M m = a m := by
  calc
    _ = (fromPoints H M a ≫ inclusion H M) ≫ evaluation H M m := (Category.assoc _ _ _).symm
    _ = Pi.lift a ≫ evaluation H M m :=
      congrArg (fun z => z ≫ evaluation H M m) (equalizer.lift_ι _ _)
    _ = a m := Pi.lift_comp_π _ m

noncomputable def pointsEquiv (T : Over S) : (T ⟶ parameter H M) ≃ (M →* (T ⟶ H)) where
  toFun := points H M T
  invFun := fromPoints H M
  left_inv a := by
    apply equalizer.hom_ext
    apply Pi.hom_ext
    intro m
    exact fromPoints_coefficient H M (points H M T a) m
  right_inv a := by
    apply MonoidHom.ext
    intro m
    exact fromPoints_coefficient H M a m

noncomputable def pointFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := M →* (T.unop ⟶ H)
  map f := ↾fun a =>
    { toFun := fun m => f.unop ≫ a m
      map_one' := by rw [a.map_one, MonObj.comp_one]
      map_mul' x y := by rw [a.map_mul, MonObj.comp_mul] }
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro a
    apply MonoidHom.ext
    intro m
    change (𝟙 T.unop) ≫ a m = a m
    exact Category.id_comp _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply MonoidHom.ext
    intro m
    change (g.unop ≫ f.unop) ≫ a m = g.unop ≫ f.unop ≫ a m
    exact Category.assoc _ _ _

noncomputable def representable : (pointFunctor H M).RepresentableBy (parameter H M) where
  homEquiv := pointsEquiv H M _
  homEquiv_comp f a := by
    apply MonoidHom.ext
    intro m
    exact Category.assoc f a (coefficient H M m)

theorem finite_etale [IsFinite H.hom] [Etale H.hom] :
    IsFinite (parameter H M).hom ∧ Etale (parameter H M).hom := by
  obtain ⟨hfin, het⟩ := FiniteEtaleLift.FiniteEtaleLimits.product_finite_etale H M
  let : IsFinite (tuples H M).hom := hfin
  let : Etale (tuples H M).hom := het
  obtain ⟨hfin', het'⟩ := FiniteEtaleLift.FiniteEtaleLimits.product_finite_etale H (RelationIndex M)
  let : IsFinite (tuples H (RelationIndex M)).hom := hfin'
  let : Etale (tuples H (RelationIndex M)).hom := het'
  exact FiniteEtaleLift.FiniteEtaleLimits.equalizer_finite_etale (relationsLeft H M) (relationsRight H M)

instance parameter_isFinite [IsFinite H.hom] [Etale H.hom] : IsFinite (parameter H M).hom :=
  (finite_etale H M).1

instance parameter_etale [IsFinite H.hom] [Etale H.hom] : Etale (parameter H M).hom :=
  (finite_etale H M).2

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.HomParametersMul.HomParameters
