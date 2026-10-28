import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantCochainCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates

/-! # Sheaf Constant Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafConstantCoordinates

noncomputable section

/-! The canonical sheafification of the genuine coefficient-lifted
constant cone is exactly the original crystalline sheafification map. -/

open _root_.CategoryTheory

universe u v w
variable {C : Type v} [Category.{w} C] (B : Type u) [CommRing B]
  (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{u+1} (ExactRestriction.Coeff (B := B)))]
  (M : CochainComplex (ModuleCat.{u} B) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

def coefficients := (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} B)
  (ModuleCat.{u+1} CR)).obj F

instance coefficients_additive : (coefficients (C := C) B).Additive where
  map_add := by intros; rfl

def sheafification := coefficients B ⋙ presheafToSheaf J (ModuleCat.{u+1} CR)

instance sheafification_additive : (sheafification B J).Additive := by
  dsimp only [sheafification]
  infer_instance

theorem map_eq :
    ((presheafToSheaf J (ModuleCat.{u+1} CR)).mapHomologicalComplex (.up ℕ)).map
      (Constant.CochainMap.map F M P a) =
    ((sheafification B J).mapHomologicalComplex (.up ℕ)).map a := by
  exact congrArg ((presheafToSheaf J (ModuleCat.{u+1} CR)).mapHomologicalComplex (.up ℕ)).map
    (ConstantCochainCoordinates.map_eq B M P a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafConstantCoordinates
