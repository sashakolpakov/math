import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.FieldPointDetection

/-! # Map Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.MapDetection.Construction

noncomputable section

/-! Universal global functions detect pointed maps by their geometric
base changes, preserving nilpotents on arbitrary base schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem universalFunction_pointed_map_eq_of_geometric_baseChanges
    {S : Scheme.{0}} (X Y : Over S) [GrpObj X] [GrpObj Y] [IsProper X.hom]
    (hX : GlobalFunctions.Construction.HasUniversalGlobalFunctions X)
    (f g : X ⟶ Y) (hf : η[X] ≫ f = η[Y]) (hg : η[X] ≫ g = η[Y])
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map g) : f = g := by
  have hz : η[X] ≫ (f / g) = η[Y] := by
    rw [GrpObj.comp_div, hf, hg, div_self']
    simp [Hom.one_def]
  have hd : f / g = 1 := IsogenyQuotient.Field.PointGroupDetection.Construction.overHom_eq_one_of_fieldPoints X Y hX.restrict (f / g) hz (by
    intro K _ s x
    rw [GrpObj.comp_div, Geometric.FieldPointDetection.Construction.overHom_fieldPoint_eq_of_geometric_baseChanges f g h s x, div_self'])
  exact div_eq_one.mp hd

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.MapDetection.Construction
