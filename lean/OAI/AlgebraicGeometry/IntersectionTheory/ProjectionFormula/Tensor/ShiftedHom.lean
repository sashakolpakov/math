import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Triangulated
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! # Shifted Hom -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ShiftedHom

noncomputable section

/-! The quotient lift of the tensor functor acts on shifted morphisms
by the native tensor functor and its shift isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)

theorem map {P Q : CochainComplex (ModuleCat.{0} R) ℤ} {a : ℤ} (f : P ⟶ Q⟦a⟧) :
    ShiftedHom.map (ShiftedHom.map f (HomotopyCategory.quotient _ _))
        (Homotopy.homotopyFunctor R K) =
      ShiftedHom.map (ShiftedHom.map f (Homotopy.complexFunctor R K))
        (HomotopyCategory.quotient _ _) := by
  have h := ShiftedHom.map_naturality f (Triangulated.liftIso R K).hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, Triangulated.liftIso,
    CategoryTheory.Quotient.lift.isLift_hom, ShiftedHom.comp_map] at h
  change _ ≫ (shiftFunctor (HomotopyCategory (ModuleCat.{0} R) (.up ℤ)) a).map
      (𝟙 ((Homotopy.homotopyFunctor R K).obj ((HomotopyCategory.quotient _ _).obj Q))) =
    (𝟙 ((Homotopy.homotopyFunctor R K).obj ((HomotopyCategory.quotient _ _).obj P))) ≫ _ at h
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ShiftedHom
