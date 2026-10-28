import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseTransitionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.CompatibleSequenceEquivalence

/-! # Cech Inverse Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechInverseLimit

noncomputable section

/-! Original integral crystalline cohomology is canonically the compatible inverse system of native Witt Čech cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def transition (n i : ℕ) :
    (WittCechTransitionData.complex p k X (n + 1)).homology i →ₗ[R]
      (WittCechTransitionData.complex p k X n).homology i :=
  (HomologicalComplex.homologyMap (WittCechTransition.map p k X n (n + 1) (Nat.le_succ n)) i).hom

def compatible (i : ℕ) : Submodule R (∀ n, (WittCechTransitionData.complex p k X n).homology i) :=
  LinearMap.ker (SequentialModuleDifference.difference R _ (fun n => transition p k X n i))

theorem mem_compatible (i : ℕ) (x : ∀ n, (WittCechTransitionData.complex p k X n).homology i) :
    x ∈ compatible p k X i ↔ ∀ n, transition p k X n i (x (n + 1)) = x n :=
  SequentialModuleDifference.difference_eq_zero_iff R _ _ x

theorem transition_coordinates (n i : ℕ) (x : (WittCechTransitionData.complex p k X (n + 1)).homology i) :
    WittCechLinearEquiv.equivalence p k X n i (transition p k X n i x) =
      Crystalline.CohomologyDifference.transition (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i
          (WittCechLinearEquiv.equivalence p k X (n + 1) i x) :=
  (WittCechLinearNaturality.naturality p k X n (n + 1) (Nat.le_succ n) i x).trans
    (congrArg (fun a => a (WittCechLinearEquiv.equivalence p k X (n + 1) i x))
      (Crystalline.InverseTransitionCoordinates.transition (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i).symm)

def boundedEquiv (i : ℕ) : compatible p k X i ≃ₗ[R]
    Crystalline.CohomologyDifference.compatible (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) i :=
  CompatibleSequenceEquivalence.equivalence R
    (fun n => (WittCechTransitionData.complex p k X n).homology i)
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i)
    (fun n => transition p k X n i)
    (fun n => Crystalline.CohomologyDifference.transition (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i)
    (fun n => WittCechLinearEquiv.equivalence p k X n i)
    (fun n x => transition_coordinates p k X n i x)

def integralEquiv (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i : ℕ) :
    Witt.Crystalline.integralCohomology p k X i ≃ₗ[R] compatible p k X i :=
  (CrystallineInverseLimit.compatibleEquiv p k X hprojective i).trans
    (boundedEquiv p k X i).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechInverseLimit
