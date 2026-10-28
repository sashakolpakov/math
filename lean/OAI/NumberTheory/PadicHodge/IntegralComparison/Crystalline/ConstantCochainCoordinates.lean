import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.CochainMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution

/-! # Constant Cochain Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantCochainCoordinates

noncomputable section

/-! The literal crystalline coefficient lift of a constant-source
cochain map agrees with postcomposition by the original coefficient functor. -/

open _root_.CategoryTheory

universe u v w
variable {C : Type v} [Category.{w} C] (B : Type u) [CommRing B]
  (M : CochainComplex (ModuleCat.{u} B) ℕ)
  (P : CochainComplex (C ⥤ ModuleCat.{u} B) ℕ)
  (a : ((Functor.const C).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)

theorem map_eq : Constant.CochainMap.map F M P a =
    ((((Functor.whiskeringRight C (ModuleCat.{u} B)
      (ModuleCat.{u+1} (ExactRestriction.Coeff (B := B)))).obj F).mapHomologicalComplex (.up ℕ)).map a) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantCochainCoordinates
