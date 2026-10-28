import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Character Average Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAveragePullback

noncomputable section

/-! Character averaging commutes with actual sheaf pullback, including the pullback of coefficient functions and of the translation action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X Y : Scheme.{u}} {G : Type v} [CommGroup G] [Fintype G]

theorem sheafCharacterAverage_map (F : X.Modules ⥤ Y.Modules) [F.Additive]
    (c : K →+* Γ(X, ⊤)) (d : K →+* Γ(Y, ⊤)) (M : X.Modules)
    (hc : ∀ r : K, F.map (Global.ModuleScalars.globalModuleScalar M (c r)) = Global.ModuleScalars.globalModuleScalar (F.obj M) (d r))
    (ρ : G →* End M) (χ : G →* Kˣ) :
    F.map (CharacterAverages.sheafCharacterAverage c M ρ χ) =
      CharacterAverages.sheafCharacterAverage d (F.obj M) ((F.mapEnd M).comp ρ) χ := by
  rw [CharacterAverageFormula.sheafCharacterAverage_formula, CharacterAverageFormula.sheafCharacterAverage_formula]
  simp only [F.map_comp, F.map_sum, hc, MonoidHom.comp_apply, Functor.mapEnd_apply]

theorem sheafCharacterAverage_pullback (f : Y ⟶ X) (c : K →+* Γ(X, ⊤))
    (M : X.Modules) (ρ : G →* End M) (χ : G →* Kˣ) :
    (Scheme.Modules.pullback f).map (CharacterAverages.sheafCharacterAverage c M ρ χ) =
      CharacterAverages.sheafCharacterAverage (f.appTop.hom.comp c) ((Scheme.Modules.pullback f).obj M)
        (((Scheme.Modules.pullback f).mapEnd M).comp ρ) χ :=
  sheafCharacterAverage_map _ c _ M (fun r => Global.ScalarBaseChange.globalModuleScalar_pullback f M (c r)) ρ χ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAveragePullback
