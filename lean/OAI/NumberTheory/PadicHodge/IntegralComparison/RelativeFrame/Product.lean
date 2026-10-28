import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientPairing

/-! # Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Product

noncomputable section

/-! The literal map from native frame PD forms to the relative crystalline
resolution preserves products, before and after the actual coefficient
functor used by bounded sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

def framePairing (a b : ℕ) :
    FormMap.frameModule F a →ₗ[B]
      FormMap.frameModule F b →ₗ[B]
        FormMap.frameModule F (a + b) := by
  let : Algebra B F.ring := F.base.toAlgebra
  exact (PD.DeRhamWedge.wedge B F.ring F.ideal F.dividedPowers a b).restrictScalars₁₂ B B

theorem map_product (U : C) (a b : ℕ)
    (x : FormMap.frameModule F a)
    (y : FormMap.frameModule F b) :
    FormMap.map H Q π F τ U (a + b) (framePairing F a b x y) =
      RelativeCrystalline.Product.sectionPairing H Q π a b (op U)
        (FormMap.map H Q π F τ U a x)
        (FormMap.map H Q π F τ U b y) := by
  let : Algebra B F.ring := F.base.toAlgebra
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact PD.DeRhamAdditiveProduct.Wedge.addMap_wedge B (Q.obj U).ring F.ring (H.obj U).ring
    F.ideal F.dividedPowers (H.obj U).ideal (H.obj U).dividedPowers
    (τ.app U).ringMap.toRingHom
    (fun n => (FormMap.map H Q π F τ U n).hom.toAddMonoidHom)
    (fun n c t => FormMap.map_symbol H Q π F τ U n c t) a b x y

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)

theorem coefficientMap_product (U : C) (a b : ℕ)
    (x : (T).obj (FormMap.frameModule F a))
    (y : (T).obj (FormMap.frameModule F b)) :
    (T).map (FormMap.map H Q π F τ U (a + b))
        (Crystalline.CoefficientPairing.lift B _ _ _ (framePairing F a b) x y) =
      Crystalline.CoefficientPairing.lift B _ _ _
        (RelativeCrystalline.Product.sectionPairing H Q π a b (op U))
        ((T).map (FormMap.map H Q π F τ U a) x)
        ((T).map (FormMap.map H Q π F τ U b) y) :=
  Crystalline.CoefficientPairing.map_lift B _ _ _
    (FormMap.map H Q π F τ U a)
    (FormMap.map H Q π F τ U b)
    (FormMap.map H Q π F τ U (a + b))
    (framePairing F a b) (RelativeCrystalline.Product.sectionPairing H Q π a b (op U))
    (map_product H Q π F τ U a b) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Product
