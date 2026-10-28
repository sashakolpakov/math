import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.BaseMapCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterClosedFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange

/-! # Universal Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.UniversalBaseChange

noncomputable section

/-! The universal embedded family itself is preserved by arbitrary change of the parameter base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) {n B N : ℕ} {r : ℕ → ℕ}
variable (hN : N ≤ B) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

theorem generatedUniversalClosedFamily_baseChange :
    (ParameterClosedFamilies.generatedParameterClosedFamily (𝟙 (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left) hflat).projectiveBaseChange
        (ParameterBaseMaps.generatedParameterBaseMap f n B r N hN) =
      ParameterClosedFamilies.generatedParameterClosedFamily (𝟙 (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).left) hflat := by
  apply Closed.Families.FlatClosedFamily.ext_affineProjective
  intro R x
  rw [Closed.Families.FlatClosedFamily.projectiveBaseChange_affine, ParameterClosedFamilies.generatedParameterClosedFamily_affine,
    ParameterClosedFamilies.generatedParameterClosedFamily_affine, Category.comp_id, Category.comp_id]
  exact BaseMapCoordinates.generatedParameterBaseMap_affineFamily f hN x hflat

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.UniversalBaseChange
