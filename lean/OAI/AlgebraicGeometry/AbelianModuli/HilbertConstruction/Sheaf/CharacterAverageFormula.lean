import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverages

/-! # Character Average Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageFormula

noncomputable section

/-! The intrinsic sheaf average is an explicit finite sum of translations followed by multiplication by the actual coefficient functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤)) (M : X.Modules)
    {G : Type v} [CommGroup G] [Fintype G]

theorem sheafCharacterAverage_formula (ρ : G →* End M) (χ : G →* Kˣ) :
    CharacterAverages.sheafCharacterAverage c M ρ χ =
      (∑ a : G, ρ a ≫ Global.ModuleScalars.globalModuleScalar M (c (χ a : K)⁻¹)) ≫
        Global.ModuleScalars.globalModuleScalar M (c (Fintype.card G : K)⁻¹) := by
  let : Algebra K (End M) := Module.SheafCoefficientAlgebra.moduleSheafCoefficientAlgebra c M
  change CharacterWeightedOperators.characterAverageOperator K G (End M) ρ χ = _
  simp only [CharacterWeightedOperators.characterAverageOperator, CharacterWeightedOperators.characterWeightedOperator, Algebra.smul_def]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageFormula
