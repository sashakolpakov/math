import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SectionEndomorphisms

/-! # Character Average Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageSectionValues

noncomputable section

/-! On every open, the actual sheaf character average acts by a finite weighted sum over the actual section action with restricted coefficient functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤))
    (M : X.Modules) {G : Type v} [CommGroup G] [Fintype G]

def schemeOpenCoefficientMap (U : X.Opens) : K →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp c

theorem sheafCharacterAverage_app (ρ : G →* End M) (χ : G →* Kˣ)
    (U : X.Opens) (s : Γ(M, U)) :
    (CharacterAverages.sheafCharacterAverage c M ρ χ).app U s =
      schemeOpenCoefficientMap c U ((Fintype.card G : K)⁻¹) •
        ∑ a : G, schemeOpenCoefficientMap c U ((χ a : K)⁻¹) • (ρ a).app U s := by
  refine (congrArg (fun p : End M => p.app U s) (CharacterAverageFormula.sheafCharacterAverage_formula c M ρ χ)).trans ?_
  change schemeOpenCoefficientMap c U ((Fintype.card G : K)⁻¹) •
      (∑ a : G, ρ a ≫ Global.ModuleScalars.globalModuleScalar M (c ((χ a : K)⁻¹))).app U s = _
  apply congrArg (fun z : Γ(M, U) => schemeOpenCoefficientMap c U ((Fintype.card G : K)⁻¹) • z)
  exact (SectionEndomorphisms.moduleSheafSum_app M U _ s).trans (Finset.sum_congr rfl (fun _ _ => rfl))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageSectionValues
