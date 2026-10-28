import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality

/-! # Product Base Change Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ProductBaseChangeCup

noncomputable section

/-! The actual tuple-product comparison for a functor preserving the
cover intersections preserves the Čech Alexander–Whitney pairing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PairingNaturality.Bilinear

universe u v s t r a
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {R : Type r} [CommRing R]
  (F : C ⥤ D) {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  (P Q T : Dᵒᵖ ⥤ ModuleCat.{a} R)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "N'" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (Functor.obj F ∘ U)

def map (P : Dᵒᵖ ⥤ ModuleCat.{a} R) :=
  (GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.cosimplicialIso F U P).hom

theorem projection_map (n : SimplexCategory) (z : Fin (n.len+1) → ι)
    (x : (BilinearPairing.cosimplicial N (F.op ⋙ P)).obj n) :
    BilinearPairing.projection N' P n z ((ProductBaseChangeCup.map F U P).app n x) =
      P.map (PreservesProduct.iso F (U ∘ z)).inv.op
        (BilinearPairing.projection N (F.op ⋙ P) n z x) :=
  ConcreteCategory.congr_hom (Pi.map_π
    (fun z : Fin (n.len+1) → ι => P.map (PreservesProduct.iso F (U ∘ z)).inv.op) z) x

variable (μ : ∀ V : Dᵒᵖ, P.obj V →ₗ[R] Q.obj V →ₗ[R] T.obj V)
  (hμ : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (x : P.obj V) (y : Q.obj V),
    T.map f (μ V x y) = μ W (P.map f x) (Q.map f y))

include hμ in
theorem pairing_natural (n : SimplexCategory)
    (x : (BilinearPairing.cosimplicial N (F.op ⋙ P)).obj n) (y : (BilinearPairing.cosimplicial N (F.op ⋙ Q)).obj n) :
    (ProductBaseChangeCup.map F U T).app n
      (BilinearPairing.pairing N (F.op ⋙ P) (F.op ⋙ Q) (F.op ⋙ T) (fun V => μ (F.op.obj V)) n x y) =
      BilinearPairing.pairing N' P Q T μ n ((ProductBaseChangeCup.map F U P).app n x) ((ProductBaseChangeCup.map F U Q).app n y) := by
  apply Module.ProductScalarKernel.element_ext
    (fun z : Fin (n.len+1) → ι => T.obj (op (∏ᶜ ((F.obj ∘ U) ∘ z))))
  intro z
  change BilinearPairing.projection N' T n z _ = BilinearPairing.projection N' T n z _
  exact (projection_map F U T n z _).trans
    ((congrArg (T.map (PreservesProduct.iso F (U ∘ z)).inv.op)
      (BilinearPairing.projection_pairing N (F.op ⋙ P) (F.op ⋙ Q) (F.op ⋙ T)
        (fun V => μ (F.op.obj V)) n z x y)).trans
      ((hμ _ _ _).trans
        ((congrArg₂ (fun x y => μ (op (∏ᶜ ((F.obj ∘ U) ∘ z))) x y)
          (projection_map F U P n z x).symm (projection_map F U Q n z y).symm).trans
          (BilinearPairing.projection_pairing N' P Q T μ n z _ _).symm)))

include hμ in
theorem cup_natural (p q : ℕ)
    (x : (BilinearPairing.cosimplicial N (F.op ⋙ P)).obj ⦋p⦌)
    (y : (BilinearPairing.cosimplicial N (F.op ⋙ Q)).obj ⦋q⦌) :
    (ProductBaseChangeCup.map F U T).app ⦋p+q⦌
      (Cosimplicial.BilinearCup.cup (BilinearPairing.cosimplicial N (F.op ⋙ P))
        (BilinearPairing.cosimplicial N (F.op ⋙ Q)) (BilinearPairing.cosimplicial N (F.op ⋙ T))
        (BilinearPairing.pairing N (F.op ⋙ P) (F.op ⋙ Q) (F.op ⋙ T) (fun V => μ (F.op.obj V))) p q x y) =
      Cosimplicial.BilinearCup.cup (BilinearPairing.cosimplicial N' P) (BilinearPairing.cosimplicial N' Q)
        (BilinearPairing.cosimplicial N' T) (BilinearPairing.pairing N' P Q T μ) p q
        ((ProductBaseChangeCup.map F U P).app ⦋p⦌ x) ((ProductBaseChangeCup.map F U Q).app ⦋q⦌ y) :=
  PairingNaturality.CosimplicialBilinearCup.cup_natural _ _ (ProductBaseChangeCup.map F U P) (ProductBaseChangeCup.map F U Q) (ProductBaseChangeCup.map F U T)
    (pairing_natural F U P Q T μ hμ) p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ProductBaseChangeCup
