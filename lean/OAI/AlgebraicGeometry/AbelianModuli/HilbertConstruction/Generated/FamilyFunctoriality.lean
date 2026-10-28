import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterClosedFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange

/-! # Family Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyFunctoriality

noncomputable section

/-! Families induced by arbitrary parameter maps commute with arbitrary test-scheme pullback as actual embedded families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T U : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ}

theorem generatedParameterClosedFamily_comp
    (g : U ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left) (f : T ⟶ U)
    (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    (ParameterClosedFamilies.generatedParameterClosedFamily g hflat).projectiveBaseChange f =
      ParameterClosedFamilies.generatedParameterClosedFamily (f ≫ g) hflat := by
  apply Closed.Families.FlatClosedFamily.ext_affineProjective
  intro R x
  rw [Closed.Families.FlatClosedFamily.projectiveBaseChange_affine, ParameterClosedFamilies.generatedParameterClosedFamily_affine,
    ParameterClosedFamilies.generatedParameterClosedFamily_affine, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyFunctoriality
