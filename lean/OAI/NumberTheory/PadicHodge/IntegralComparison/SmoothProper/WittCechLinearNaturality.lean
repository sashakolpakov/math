import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLevelCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyTransport

/-! # Witt Cech Linear Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearNaturality

noncomputable section

/-! The native Witt Čech-to-original-crystalline linear equivalence is compatible with every bounded-level transition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.map (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n m hnm

theorem transport (i : ℕ) (x : (WittCechTransitionData.complex p k X m).homology i) :
    ((Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R (WittCechTransitionData.complex p k X n) i).trans
      (WittCechCohomology.homologyIso p k X n i).toLinearEquiv)
        (HomologicalComplex.homologyMap (WittCechTransition.map p k X n m hnm) i x) =
      g i (((Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R (WittCechTransitionData.complex p k X m) i).trans
        (WittCechCohomology.homologyIso p k X m i).toLinearEquiv) x) :=
  Lifted.HomologyTransport.naturality.{u + 1, u + 1, u + 2} R
    (WittCechTransition.map p k X n m hnm) i
    (WittCechCohomology.homologyIso p k X m i)
    (WittCechCohomology.homologyIso p k X n i) (ModuleCat.ofHom (g i))
    (WittCechLevelCohomology.homology p k X n m hnm i) x

theorem naturality (i : ℕ) (x : (WittCechTransitionData.complex p k X m).homology i) :
    WittCechLinearEquiv.equivalence p k X n i
      (HomologicalComplex.homologyMap (WittCechTransition.map p k X n m hnm) i x) =
        g i (WittCechLinearEquiv.equivalence p k X m i x) := by
  rw [WittCechLinearCoordinates.equivalence,
    WittCechLinearCoordinates.equivalence]
  exact transport p k X n m hnm i x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearNaturality
