import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality

/-! # Refinement Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementCup

noncomputable section

/-! The literal Čech refinement preserves the product induced by a
natural bilinear pairing of the original coefficient presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality.Bilinear

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a r
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {R : Type r} [CommRing R] {ι κ : Type}
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (P Q T : Cᵒᵖ ⥤ ModuleCat.{a} R)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "N'" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

theorem projection_map (n : SimplexCategory) (i : ((N').obj (op n)).I)
    (x : (BilinearPairing.cosimplicial N P).obj n) :
    BilinearPairing.projection N' P n i ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r P).app n x) =
      P.map (((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.nerveMap U V r).app (op n)).φ i).op
        (BilinearPairing.projection N P n (((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.nerveMap U V r).app (op n)).f i) x) :=
  ConcreteCategory.congr_hom (Pi.lift_comp_π _ i) x

variable (μ : ∀ W, P.obj W →ₗ[R] Q.obj W →ₗ[R] T.obj W)
  (hμ : ∀ {W Z : Cᵒᵖ} (f : W ⟶ Z) (x : P.obj W) (y : Q.obj W),
    T.map f (μ W x y) = μ Z (P.map f x) (Q.map f y))

include hμ in
theorem pairing_map (n : SimplexCategory)
    (x : (BilinearPairing.cosimplicial N P).obj n) (y : (BilinearPairing.cosimplicial N Q).obj n) :
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r T).app n (BilinearPairing.pairing N P Q T μ n x y) =
      BilinearPairing.pairing N' P Q T μ n
        ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r P).app n x)
        ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r Q).app n y) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => T.obj (op (((N').obj (op n)).obj i)))
  intro i
  change BilinearPairing.projection N' T n i _ = BilinearPairing.projection N' T n i _
  erw [projection_map, BilinearPairing.projection_pairing, BilinearPairing.projection_pairing,
    projection_map, projection_map]
  exact hμ _ _ _

include hμ in
theorem cup_map (p q : ℕ)
    (x : (BilinearPairing.cosimplicial N P).obj ⦋p⦌) (y : (BilinearPairing.cosimplicial N Q).obj ⦋q⦌) :
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r T).app ⦋p+q⦌
      (Cosimplicial.BilinearCup.cup (BilinearPairing.cosimplicial N P) (BilinearPairing.cosimplicial N Q)
        (BilinearPairing.cosimplicial N T) (BilinearPairing.pairing N P Q T μ) p q x y) =
    Cosimplicial.BilinearCup.cup (BilinearPairing.cosimplicial N' P) (BilinearPairing.cosimplicial N' Q)
      (BilinearPairing.cosimplicial N' T) (BilinearPairing.pairing N' P Q T μ) p q
      ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r P).app ⦋p⦌ x)
      ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r Q).app ⦋q⦌ y) :=
  PairingNaturality.CosimplicialBilinearCup.cup_natural _ _
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r P)
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r Q)
    (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.cosimplicialMap U V r T)
    (pairing_map U V r P Q T μ hμ) p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementCup
