import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.OperationGroupIsomorphisms

/-! # Iso Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.IsoOperations

noncomputable section

/-! A genuine group isomorphism transports the actual three operations,
not merely their induced maps on geometric points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {X Y : Over S} [GrpObj X] [GrpObj Y]

theorem FamilyGroupOperations.ofGrpObj_ofIso (e : X ≅ Y) [IsMonHom e.hom] :
    (Operations.FamilyGroupOperations.ofGrpObj X).ofIso e = Operations.FamilyGroupOperations.ofGrpObj Y := by
  apply Operations.FamilyGroupOperations.ext
  · exact IsMonHom.one_hom e.hom
  · change (e.inv ⊗ₘ e.inv) ≫ μ[X] ≫ e.hom = μ[Y]
    rw [IsMonHom.mul_hom e.hom, ← Category.assoc, tensorHom_comp_tensorHom,
      e.inv_hom_id, id_tensorHom_id, Category.id_comp]
  · change e.inv ≫ ι[X] ≫ e.hom = ι[Y]
    have hi : ι[X] ≫ e.hom = e.hom ≫ ι[Y] := by
      simpa only [Hom.inv_def, Category.id_comp] using GrpObj.inv_comp (𝟙 X) e.hom
    rw [hi, e.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.IsoOperations
