import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageFormula

/-! # Character Average Intertwining -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageIntertwining

noncomputable section

/-! An actual map intertwining group actions also intertwines their character averaging projectors. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤))
    {M N : X.Modules} {G : Type v} [CommGroup G] [Fintype G]

theorem sheafCharacterAverage_intertwines (ρ : G →* End M) (σ : G →* End N)
    (φ : M ⟶ N) (hφ : ∀ a, ρ a ≫ φ = φ ≫ σ a) (χ : G →* Kˣ) :
    CharacterAverages.sheafCharacterAverage c M ρ χ ≫ φ = φ ≫ CharacterAverages.sheafCharacterAverage c N σ χ := by
  have hs : (∑ a : G, ρ a ≫ Global.ModuleScalars.globalModuleScalar M (c (χ a : K)⁻¹)) ≫ φ =
      φ ≫ (∑ a : G, σ a ≫ Global.ModuleScalars.globalModuleScalar N (c (χ a : K)⁻¹)) := by
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Category.assoc, Global.ModuleScalars.globalModuleScalar_natural, ← Category.assoc, hφ a, Category.assoc]
  rw [CharacterAverageFormula.sheafCharacterAverage_formula, CharacterAverageFormula.sheafCharacterAverage_formula,
    Category.assoc, Global.ModuleScalars.globalModuleScalar_natural, ← Category.assoc, hs, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageIntertwining
