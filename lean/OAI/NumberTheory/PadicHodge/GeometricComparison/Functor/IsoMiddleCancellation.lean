import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso

/-! # Iso Middle Cancellation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.IsoMiddleCancellation.FunctorIsoMiddleCancellation

/-! Applying a functor cancels the same intermediate comparison
isomorphism in a composite of original comparison maps. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (S : C ⥤ D) (H : D ⥤ E) {M : D} {X Y Z : C}
  (a : M ⟶ S.obj Y) (e : X ≅ Y) (b : Y ⟶ Z)

theorem square : H.map (a ≫ S.map e.inv) ≫ (S ⋙ H).map (e.hom ≫ b) = H.map a ≫ (S ⋙ H).map b := by
  have h := ((S ⋙ H).mapIso e).inv_hom_id_assoc ((S ⋙ H).map b)
  exact (congrArg₂ (fun x y => x ≫ y) (H.map_comp a (S.map e.inv))
    ((S ⋙ H).map_comp e.hom b)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun q => H.map a ≫ q) h))

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.IsoMiddleCancellation.FunctorIsoMiddleCancellation
