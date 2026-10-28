import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands

/-! # Character Eigenmaps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterEigenmaps

noncomputable section

/-! The actual sheaf averages and their equalizer summands transform by their characters. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤)) (M : X.Modules)
    {G : Type v} [CommGroup G] [Fintype G]

theorem sheafCharacterAverage_eigen (ρ : G →* End M) (χ : G →* Kˣ) (a : G) :
    CharacterAverages.sheafCharacterAverage c M ρ χ ≫ ρ a =
      CharacterAverages.sheafCharacterAverage c M ρ χ ≫ Global.ModuleScalars.globalModuleScalar M (c (χ a : K)) := by
  let : Algebra K (End M) := Module.SheafCoefficientAlgebra.moduleSheafCoefficientAlgebra c M
  have h := CharacterWeightedOperators.characterAverageOperator_left K G (End M) ρ χ a
  rw [Algebra.smul_def] at h
  exact h

theorem sheafCharacterSummand_eigen (ρ : G →* End M) (χ : G →* Kˣ) (a : G) :
    IdempotentSheafSummands.idempotentSheafInclusion (CharacterAverages.sheafCharacterAverage c M ρ χ) ≫ ρ a =
      Global.ModuleScalars.globalModuleScalar (IdempotentSheafSummands.idempotentSheafSummand (CharacterAverages.sheafCharacterAverage c M ρ χ)) (c (χ a : K)) ≫
        IdempotentSheafSummands.idempotentSheafInclusion (CharacterAverages.sheafCharacterAverage c M ρ χ) := by
  let p := CharacterAverages.sheafCharacterAverage c M ρ χ
  calc
    IdempotentSheafSummands.idempotentSheafInclusion p ≫ ρ a = (IdempotentSheafSummands.idempotentSheafInclusion p ≫ p) ≫ ρ a := by
      rw [IdempotentSheafSummands.idempotentSheafInclusion_fixed]
    _ = (IdempotentSheafSummands.idempotentSheafInclusion p ≫ p) ≫ Global.ModuleScalars.globalModuleScalar M (c (χ a : K)) := by
      rw [Category.assoc, sheafCharacterAverage_eigen, ← Category.assoc]
    _ = IdempotentSheafSummands.idempotentSheafInclusion p ≫ Global.ModuleScalars.globalModuleScalar M (c (χ a : K)) := by
      rw [IdempotentSheafSummands.idempotentSheafInclusion_fixed]
    _ = Global.ModuleScalars.globalModuleScalar (IdempotentSheafSummands.idempotentSheafSummand p) (c (χ a : K)) ≫
        IdempotentSheafSummands.idempotentSheafInclusion p := (Global.ModuleScalars.globalModuleScalar_natural _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterEigenmaps
