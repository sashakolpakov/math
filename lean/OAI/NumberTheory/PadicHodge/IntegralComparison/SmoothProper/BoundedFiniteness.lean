import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechExactSequence
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedZeroFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactHomologyFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientNoetherian

/-! # Bounded Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedFiniteness

noncomputable section

/-! Unconditional finite generation of every original bounded crystalline cohomology group of a smooth proper projective scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

theorem cech_zero (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i : ℕ) :
    Module.Finite R ((WittCechTransitionData.complex p k X 0).homology i) := by
  let : Module.Finite R
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0 i) :=
    BoundedZeroFiniteness.finite p k X hprojective i
  exact Module.Finite.equiv (WittCechLinearEquiv.equivalence p k X 0 i).symm

theorem cech_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n i : ℕ) :
    Module.Finite R ((WittCechTransitionData.complex p k X n).homology i) := by
  let : IsNoetherianRing R := Witt.CoefficientNoetherian.coefficient p k
  let hzero : Module.Finite R ((WittCechTransitionData.complex p k X 0).homology i) := cech_zero p k X hprojective i
  induction n with
  | zero => exact hzero
  | succ n ih =>
    let : Module.Finite R ((WittCechExactSequence.sequence p k X n).X₁.homology i) := ih
    let : Module.Finite R ((WittCechExactSequence.sequence p k X n).X₃.homology i) := hzero
    exact ExactHomologyFiniteness.homology R (WittCechExactSequence.sequence p k X n)
      (WittCechExactSequence.shortExact p k X n) i

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n i : ℕ) :
    Module.Finite R
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) := by
  let : Module.Finite R ((WittCechTransitionData.complex p k X n).homology i) := cech_finite p k X hprojective n i
  exact Module.Finite.equiv (WittCechLinearEquiv.equivalence p k X n i)

theorem finite_type (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n i : ℕ) :
    Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) := by
  let : Module.Finite R
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) :=
    finite p k X hprojective n i
  exact Bounded.WittCohomologyFinite.finite p k (Witt.Crystalline.wittStructureMap p k X) n i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedFiniteness
