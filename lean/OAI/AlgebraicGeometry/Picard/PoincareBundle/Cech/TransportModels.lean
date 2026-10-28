import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.FlatCoordinates

/-! # Transport Models -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TransportModels

noncomputable section

/-!
# Coordinate transport in the common triple tensor model
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ThirdModel OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.FlatCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Transport

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

local notation "V" => (S ⊗[R] S) ⊗[R] S

/-- Additive maps out of a triple-ring scalar extension are determined on pure tensors. -/
theorem tripleTensor_ext (i : S →+* V) {N : Type u} [AddCommGroup N]
    (f g : TripleGluing.slotModule R S M i → N)
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ (a b c : S) (m : M),
      f (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[S,i] m) =
        g (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[S,i] m))
    (z : TripleGluing.slotModule R S M i) : f z = g z := by
  have hf0 : f 0 = 0 := add_eq_left.mp (by simpa only [zero_add] using (hf 0 0).symm)
  have hg0 : g 0 = 0 := add_eq_left.mp (by simpa only [zero_add] using (hg 0 0).symm)
  have hz : f 0 = g 0 := hf0.trans hg0.symm
  have ht (m : M) : ((0 : V) ⊗ₜ[S,i] m : TripleGluing.slotModule R S M i) = 0 :=
    TensorProduct.zero_tmul _ _
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact (hf x y).trans ((congrArg₂ (· + ·) hx hy).trans (hg x y).symm)
  | tmul v m =>
      induction v using TensorProduct.inductionOn with
      | add x y hx hy =>
          erw [add_tmul, hf, hx, hy, hg]
      | tmul u c =>
          induction u using TensorProduct.inductionOn with
          | add x y hx hy => erw [add_tmul, add_tmul, hf, hx, hy, hg]
          | tmul a b => exact h a b c m

/-- Transposing the second and third coordinates swaps the two coefficient tensor factors. -/
theorem firstModel_swap23 (z : TripleGluing.slotModule R S M (TripleGluing.slot1 R S)) :
    (TripleGluing.firstFlatModel R S M).hom (Transport.swap23OnFirst R S M z) =
      TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)
        ((TripleGluing.firstFlatModel R S M).hom z) := by
  refine tripleTensor_ext R S M (TripleGluing.slot1 R S) (N := TripleExtension.tripleModule R S M)
    (fun x => (TripleGluing.firstFlatModel R S M).hom (Transport.swap23OnFirst R S M x))
    (fun x => TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)
      ((TripleGluing.firstFlatModel R S M).hom x)) ?_ ?_ ?_ z
  · intro x y
    erw [map_add, map_add]
  · intro x y
    erw [map_add, map_add]
  · intro a b c m
    exact (FlatCoordinates.firstFlatModel_tmul R S M a c b m).trans
      (congrArg (TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M))
        (FlatCoordinates.firstFlatModel_tmul R S M a b c m)).symm

/-- Transporting the second pullback to the third preserves these tensor coordinates. -/
theorem thirdModel_swap23 (z : TripleGluing.slotModule R S M (TripleGluing.slot2 R S)) :
    ThirdModel.thirdFlatModel R S M (Transport.swap23OnSecond R S M z) = (TripleGluing.secondFlatModel R S M).hom z := by
  refine tripleTensor_ext R S M (TripleGluing.slot2 R S) (N := TripleExtension.tripleModule R S M)
    (fun x => ThirdModel.thirdFlatModel R S M (Transport.swap23OnSecond R S M x))
    (fun x => (TripleGluing.secondFlatModel R S M).hom x) ?_ ?_ ?_ z
  · intro x y
    erw [map_add, map_add]
  · intro x y
    exact ((TripleGluing.secondFlatModel R S M).hom).hom.map_add x y
  · intro a b c m
    exact (ThirdModel.thirdFlatModel_tmul R S M a c b m).trans (FlatCoordinates.secondFlatModel_tmul R S M a b c m).symm

/-- Transporting the first pullback to the second preserves these tensor coordinates. -/
theorem secondModel_swap12 (z : TripleGluing.slotModule R S M (TripleGluing.slot1 R S)) :
    (TripleGluing.secondFlatModel R S M).hom (Transport.swap12OnFirst R S M z) = (TripleGluing.firstFlatModel R S M).hom z := by
  refine tripleTensor_ext R S M (TripleGluing.slot1 R S) (N := TripleExtension.tripleModule R S M)
    (fun x => (TripleGluing.secondFlatModel R S M).hom (Transport.swap12OnFirst R S M x))
    (fun x => (TripleGluing.firstFlatModel R S M).hom x) ?_ ?_ ?_ z
  · intro x y
    erw [map_add, map_add]
  · intro x y
    exact ((TripleGluing.firstFlatModel R S M).hom).hom.map_add x y
  · intro a b c m
    exact (FlatCoordinates.secondFlatModel_tmul R S M b a c m).trans (FlatCoordinates.firstFlatModel_tmul R S M a b c m).symm

/-- Transposition of the first two coordinates swaps the coefficient factors of the third model. -/
theorem thirdModel_swap12 (z : TripleGluing.slotModule R S M (TripleGluing.slot3 R S)) :
    ThirdModel.thirdFlatModel R S M (Transport.swap12OnThird R S M z) =
      TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)
        (ThirdModel.thirdFlatModel R S M z) := by
  refine tripleTensor_ext R S M (TripleGluing.slot3 R S) (N := TripleExtension.tripleModule R S M)
    (fun x => ThirdModel.thirdFlatModel R S M (Transport.swap12OnThird R S M x))
    (fun x => TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)
      (ThirdModel.thirdFlatModel R S M x)) ?_ ?_ ?_ z
  · intro x y
    erw [map_add, map_add]
  · intro x y
    erw [map_add, map_add]
  · intro a b c m
    exact (ThirdModel.thirdFlatModel_tmul R S M b a c m).trans
      (congrArg (TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M))
        (ThirdModel.thirdFlatModel_tmul R S M a b c m)).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TransportModels
