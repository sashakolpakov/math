import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.FieldPointDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GlobalFunctions

/-! # Map Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.MapDetection.Construction

noncomputable section

/-! Geometric fibers detect pointed maps from a proper smooth
connected group over a Noetherian base, retaining nilpotents in the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem noetherian_pointed_map_eq_of_geometric_baseChanges
    {S : Scheme.{0}} [IsLocallyNoetherian S] (X Y : Over S) [GrpObj X] [GrpObj Y]
    [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (f g : X ⟶ Y) (hf : η[X] ≫ f = η[Y]) (hg : η[X] ≫ g = η[Y])
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map g) : f = g := by
  have hσ : η[X].left ≫ X.hom = 𝟙 S := Over.w η[X]
  have hΓ (V : S.Opens) : IsIso (X.hom ∣_ V).appTop :=
    GlobalFunctions.Construction.noetherian_globalFunctions_isIso (X.hom ∣_ V)
      (AbelianModuli.HilbertConstruction.Family.SectionRestriction.familySectionRestrict X.hom η[X].left hσ V)
      (AbelianModuli.HilbertConstruction.Family.SectionRestriction.familySectionRestrict_projection X.hom η[X].left hσ V)
  have hz : η[X] ≫ (f / g) = η[Y] := by
    rw [GrpObj.comp_div, hf, hg, div_self']
    simp [Hom.one_def]
  have hd : f / g = 1 := IsogenyQuotient.Field.PointGroupDetection.Construction.overHom_eq_one_of_fieldPoints X Y hΓ (f / g) hz (by
    intro K _ s x
    rw [GrpObj.comp_div, Geometric.FieldPointDetection.Construction.overHom_fieldPoint_eq_of_geometric_baseChanges f g h s x, div_self'])
  exact div_eq_one.mp hd

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.MapDetection.Construction
