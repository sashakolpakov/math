import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericIdentities
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionDescent

/-! # Group Map Reflection -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupMapReflection

noncomputable section

/-! The two group-homomorphism identities reflect from a dominant
base change for smooth arithmetic models. Only the required two
map spaces need injectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Functor
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem isMonHom_of_map_injective
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {X Y : C} [MonObj X] [MonObj Y]
    (f : X ⟶ Y) [IsMonHom (F.map f)]
    (hOne : Function.Injective (F.map : (𝟙_ C ⟶ Y) → _))
    (hMul : Function.Injective (F.map : (X ⊗ X ⟶ Y) → _)) : IsMonHom f where
  one_hom := by
    apply hOne
    apply (cancel_epi (LaxMonoidal.ε F)).mp
    have h := IsMonHom.one_hom (F.map f)
    change (LaxMonoidal.ε F ≫ F.map MonObj.one) ≫ F.map f =
      LaxMonoidal.ε F ≫ F.map MonObj.one at h
    simpa only [Category.assoc, F.map_comp] using h
  mul_hom := by
    apply hMul
    apply (cancel_epi (LaxMonoidal.μ F X X)).mp
    have h := IsMonHom.mul_hom (F.map f)
    change (LaxMonoidal.μ F X X ≫ F.map MonObj.mul) ≫ F.map f =
      (F.map f ⊗ₘ F.map f) ≫ LaxMonoidal.μ F Y Y ≫ F.map MonObj.mul at h
    rw [LaxMonoidal.μ_natural_assoc] at h
    simpa only [Category.assoc, F.map_comp] using h

theorem isMonHom_of_dominant_baseChange
    {S T : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S]
    (u : T ⟶ S) [IsDominant u] {X Y : Over S} [GrpObj X] [GrpObj Y]
    [Smooth X.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsMonHom ((Over.pullback u).map f)] : IsMonHom f := by
  apply isMonHom_of_map_injective (Over.pullback u) f
  · intro a b hab
    let : Smooth (𝟙_ (Over S)).hom := inferInstanceAs (Smooth (𝟙 S))
    exact IntegralModel.GenericIdentities.smooth_hom_eq_of_dominant_base_change u a b hab
  · intro a b hab
    let : Smooth (X ⊗ X).hom := inferInstanceAs
      (Smooth (CategoryTheory.Limits.pullback.fst X.hom X.hom ≫ X.hom))
    exact IntegralModel.GenericIdentities.smooth_hom_eq_of_dominant_base_change u a b hab

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupMapReflection
