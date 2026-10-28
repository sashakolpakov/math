import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarComplexCohomology

/-! # Cech Scalar System -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechScalarSystem

noncomputable section

/-! The native Witt Čech cohomology groups form a finite scalar-exact inverse system with their actual transition maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def map (n m : ℕ) (hnm : n ≤ m) (i : ℕ) : (WittCechTransitionData.complex p k X m).homology i →ₗ[R] (WittCechTransitionData.complex p k X n).homology i :=
  (HomologicalComplex.homologyMap (WittCechTransition.map p k X n m hnm) i).hom

def inclusion (n i : ℕ) : (WittCechTransitionData.complex p k X n).homology i →ₗ[R] (WittCechTransitionData.complex p k X (n + 1)).homology i :=
  (HomologicalComplex.homologyMap (WittCechExactSequence.sequence p k X n).f i).hom

theorem identity (n i : ℕ) : map p k X n n le_rfl i = LinearMap.id := by
  have h := congrArg (fun a => HomologicalComplex.homologyMap a i)
    (WittCechTransitionComposition.identity p k X n)
  rw [HomologicalComplex.homologyMap_id] at h
  exact congrArg (fun a => a.hom) h

theorem composition (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (i : ℕ) (x : (WittCechTransitionData.complex p k X l).homology i) :
    map p k X n l (hnm.trans hml) i x = map p k X n m hnm i (map p k X m l hml i x) := by
  have h := congrArg (fun a => HomologicalComplex.homologyMap a i)
    (WittCechTransitionComposition.composition p k X n m l hnm hml)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact (congrArg (fun a => a x) h).symm

theorem map_inclusion (n i : ℕ) (x : (WittCechTransitionData.complex p k X n).homology i) :
    map p k X n (n + 1) (Nat.le_succ n) i (inclusion p k X n i x) = (p : R) • x :=
  ScalarComplexCohomology.cohomology_inclusion_quotient
    (WittCechTransition.map p k X n (n + 1) (Nat.le_succ n))
    (WittCechTermKernel.surjective p k X n (n + 1) (Nat.le_succ n)) (p : R)
    (WittCechTermKernel.successive_kernel p k X n) i x

theorem inclusion_map (n i : ℕ) (x : (WittCechTransitionData.complex p k X (n + 1)).homology i) :
    inclusion p k X n i (map p k X n (n + 1) (Nat.le_succ n) i x) = (p : R) • x :=
  ScalarComplexCohomology.cohomology_quotient_inclusion
    (WittCechTransition.map p k X n (n + 1) (Nat.le_succ n))
    (WittCechTermKernel.surjective p k X n (n + 1) (Nat.le_succ n)) (p : R)
    (WittCechTermKernel.successive_kernel p k X n) i x

theorem exact (n i : ℕ) (x : (WittCechTransitionData.complex p k X (n + 1)).homology i) :
    map p k X 0 (n + 1) (Nat.zero_le (n + 1)) i x = 0 ↔ ∃ y, inclusion p k X n i y = x := by
  have h := (WittCechExactSequence.shortExact p k X n).homology_exact₂ i
  exact (SetLike.ext_iff.mp h.moduleCat_range_eq_ker x).symm

theorem power_zero (n i : ℕ) (x : (WittCechTransitionData.complex p k X n).homology i) : (p : R) ^ (n + 1) • x = 0 := by
  let e := WittCechLinearEquiv.equivalence p k X n i
  apply e.injective
  rw [map_smul, map_zero]
  exact Bounded.CohomologyTorsion.cohomology_smul_zero (Witt.Crystalline.wittStructureMap p k X) n i (e x)

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n i : ℕ) :
    Finite ((WittCechTransitionData.complex p k X n).homology i) := by
  let : Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) :=
    BoundedFiniteness.finite_type p k X hprojective n i
  exact Finite.of_injective (WittCechLinearEquiv.equivalence p k X n i)
    (WittCechLinearEquiv.equivalence p k X n i).injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechScalarSystem
