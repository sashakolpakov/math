import OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields

/-! # Dominant Residue Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension

noncomputable section

/-! ProjectiveCohomology's actual generic-stalk scalar extension has the native scheme residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem scheme_stalkCongr_eqToHom (X : Scheme) {x y : X} (h : x = y) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom =
      eqToHom (congrArg (fun z => X.presheaf.stalk z) h) := by
  subst y
  exact X.presheaf.stalkSpecializes_refl x

theorem dominantFunctionFieldMap_eq_genericFieldMap {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    DominantFunctionField.Dimension.dominantFunctionFieldMap f = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f (DominantFunctionField.Dimension.dominant_genericPoint f) := by
  rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, scheme_stalkCongr_eqToHom Y (DominantFunctionField.Dimension.dominant_genericPoint f).symm]
  rfl

theorem dominantFunctionField_finrank_eq_residueDegree {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    letI := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
    Module.finrank Y.functionField X.functionField = f.residueDegree (genericPoint X) := by
  unfold DominantFunctionField.Dimension.dominantFunctionFieldAlgebra
  rw [dominantFunctionFieldMap_eq_genericFieldMap]
  exact IntersectionTheory.ProjectionFormula.Support.Fields.genericFieldMap_finrank_eq_residueDegree f (DominantFunctionField.Dimension.dominant_genericPoint f)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantResidueDegree.Dimension
