import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafCoefficientAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAverageIdempotents
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.CharacterAverageSum

/-! # Character Averages -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverages

noncomputable section

/-! Intrinsic character averages are actual module-sheaf endomorphisms, with orthogonal idempotent and sum-to-identity laws. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤)) (M : X.Modules)
    {G : Type v} [CommGroup G] [Fintype G]

def sheafCharacterAverage (ρ : G →* End M) (χ : G →* Kˣ) : End M := by
  let : Algebra K (End M) := Module.SheafCoefficientAlgebra.moduleSheafCoefficientAlgebra c M
  exact CharacterWeightedOperators.characterAverageOperator K G (End M) ρ χ

theorem sheafCharacterAverage_idempotent (ρ : G →* End M) (χ : G →* Kˣ)
    (hG : (Fintype.card G : K) ≠ 0) :
    sheafCharacterAverage c M ρ χ ≫ sheafCharacterAverage c M ρ χ = sheafCharacterAverage c M ρ χ := by
  let : Algebra K (End M) := Module.SheafCoefficientAlgebra.moduleSheafCoefficientAlgebra c M
  exact CharacterAverageIdempotents.characterAverageOperator_idempotent K G (End M) ρ χ hG

theorem sheafCharacterAverage_orthogonal (ρ : G →* End M) (χ ψ : G →* Kˣ)
    (hG : (Fintype.card G : K) ≠ 0) (h : ψ ≠ χ) :
    sheafCharacterAverage c M ρ ψ ≫ sheafCharacterAverage c M ρ χ = 0 := by
  let : Algebra K (End M) := Module.SheafCoefficientAlgebra.moduleSheafCoefficientAlgebra c M
  exact CharacterAverageIdempotents.characterAverageOperator_orthogonal K G (End M) ρ χ ψ hG h

theorem sheafCharacterAverage_sum [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    [Fintype (G →* Kˣ)] (ρ : G →* End M) (hG : (Fintype.card G : K) ≠ 0) :
    ∑ χ : G →* Kˣ, sheafCharacterAverage c M ρ χ = 𝟙 M := by
  let : Algebra K (End M) := Module.SheafCoefficientAlgebra.moduleSheafCoefficientAlgebra c M
  exact Abelian.CharacterAverageSum.characterAverageOperator_sum K G (End M) ρ hG

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverages
