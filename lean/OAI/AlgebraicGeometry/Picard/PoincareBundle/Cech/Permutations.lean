import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

/-! # Permutations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Permutations

noncomputable section

/-!
# Permuting coordinates of the actual affine triple fiber product
-/

open TensorProduct
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "U" => S ⊗[R] S
local notation "V" => (S ⊗[R] S) ⊗[R] S

/-- Interchange the first and second coordinates. -/
def swap12 : V ≃ₐ[R] V :=
  Algebra.TensorProduct.congr (Algebra.TensorProduct.comm R S S) (AlgEquiv.refl : S ≃ₐ[R] S)

/-- Interchange the second and third coordinates. -/
def swap23 : V ≃ₐ[R] V :=
  (Algebra.TensorProduct.assoc R R R S S S).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[R] S)
      (Algebra.TensorProduct.comm R S S)).trans
        (Algebra.TensorProduct.assoc R R R S S S).symm)

@[simp]
theorem swap12_tmul (a b c : S) :
    swap12 R S ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = (b ⊗ₜ[R] a) ⊗ₜ[R] c := rfl

@[simp]
theorem swap23_tmul (a b c : S) :
    swap23 R S ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = (a ⊗ₜ[R] c) ⊗ₜ[R] b := rfl

theorem swap12_involutive (z : V) : swap12 R S (swap12 R S z) = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul a b => rfl

theorem swap23_involutive (z : V) : swap23 R S (swap23 R S z) = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul a b => rfl

theorem swap23_slot1 (s : S) : swap23 R S (TripleGluing.slot1 R S s) = TripleGluing.slot1 R S s := rfl
theorem swap23_slot2 (s : S) : swap23 R S (TripleGluing.slot2 R S s) = TripleGluing.slot3 R S s := rfl
theorem swap23_slot3 (s : S) : swap23 R S (TripleGluing.slot3 R S s) = TripleGluing.slot2 R S s := rfl

theorem swap12_slot1 (s : S) : swap12 R S (TripleGluing.slot1 R S s) = TripleGluing.slot2 R S s := rfl
theorem swap12_slot2 (s : S) : swap12 R S (TripleGluing.slot2 R S s) = TripleGluing.slot1 R S s := rfl
theorem swap12_slot3 (s : S) : swap12 R S (TripleGluing.slot3 R S s) = TripleGluing.slot3 R S s := rfl

/-- The first-to-third gluing square is the transposed first-to-second square. -/
theorem swap23_pair12 (z : U) : swap23 R S (TripleGluing.pair12 R S z) = TripleGluing.pair13 R S z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => rfl

/-- The second-to-third gluing square is the transposed first-to-third square. -/
theorem swap12_pair13 (z : U) : swap12 R S (TripleGluing.pair13 R S z) = TripleGluing.pair23 R S z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Permutations
