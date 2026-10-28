import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction

/-! # Module Sheaf Restriction Carrier -/

namespace OAI.AlgebraicGeometry.Sheaves.ModuleSheafRestrictionCarrier.HilbertConstruction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem underlyingModuleSheafRestriction {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (AbelianModuli.HilbertConstruction.TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) =
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).obj (M.restrict U.ι) := by
  rfl

end

end OAI.AlgebraicGeometry.Sheaves.ModuleSheafRestrictionCarrier.HilbertConstruction
