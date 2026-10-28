import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyCoordinates

/-! # Witt Cech Linear Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearCoordinates

noncomputable section

/-! Factor the native linear cohomology comparison into its universe lift and its original Ext isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

theorem equivalence (n i : ℕ) : WittCechLinearEquiv.equivalence p k X n i =
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (WittCechTransitionData.complex p k X n) i).trans
        (WittCechCohomology.homologyIso p k X n i).toLinearEquiv := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearCoordinates
