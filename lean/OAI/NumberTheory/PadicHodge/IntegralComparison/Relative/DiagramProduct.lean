import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product

/-! # Diagram Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramProduct

noncomputable section

/-! Actual changes of crystalline frame preserve the native PD product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData
universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H K Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.complex K Q ρ
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap.map H K Q π ρ θ hθ

theorem map_pairing (a b : ℕ) (U : Cᵒᵖ)
    (x : ((P).X a).obj U) (y : ((P).X b).obj U) :
    ((M).f (a + b)).app U (RelativeCrystalline.Product.sectionPairing K Q ρ a b U x y) =
      RelativeCrystalline.Product.sectionPairing H Q π a b U
        (((M).f a).app U x) (((M).f b).app U y) := by
  let : Algebra (Q.obj U.unop).ring (K.obj U.unop).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U.unop
  let : Algebra (Q.obj U.unop).ring (H.obj U.unop).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U.unop
  exact PD.DeRhamAdditiveProduct.Wedge.addMap_wedge (Q.obj U.unop).ring (Q.obj U.unop).ring
    (K.obj U.unop).ring (H.obj U.unop).ring
    (K.obj U.unop).ideal (K.obj U.unop).dividedPowers
    (H.obj U.unop).ideal (H.obj U.unop).dividedPowers
    (θ.app U.unop).ringMap.toRingHom
    (fun n => (DiagramFormMap.map H K Q π ρ θ hθ U.unop n).hom.toAddMonoidHom)
    (fun n c t => DiagramFormMap.map_symbol H K Q π ρ θ hθ U.unop n c t)
    a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramProduct
