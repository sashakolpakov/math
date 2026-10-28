import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Cover

/-! # Positive Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover.Comparison

noncomputable section

/-! Affine-cover independence at any explicitly positive degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (M : X.left.Modules) [M.IsQuasicoherent]

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R

def iso (i : ℕ) (hi : 0 < i) :
    (G).obj ((DimensionBound.complex R X M U).homology i) ≅
      (G).obj ((DimensionBound.complex R X M V).homology i) := by
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ n => exact Cover.Comparison.iso R X U V hU hV haU haV M n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover.Comparison
