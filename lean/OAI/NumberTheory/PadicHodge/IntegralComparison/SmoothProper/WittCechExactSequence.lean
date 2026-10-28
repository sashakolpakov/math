import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTermKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarComplexSequence

/-! # Witt Cech Exact Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechExactSequence

noncomputable section

/-! The actual global Witt frame Čech complexes form the successive short exact sequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def sequence (n : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u + 1} R) ℕ) :=
  SurjectiveScalarComplexSequence.sequence
    (WittCechTransition.map p k X n (n + 1) (Nat.le_succ n))
    (WittCechTermKernel.surjective p k X n (n + 1) (Nat.le_succ n)) (p : R)
    (WittCechTermKernel.successive_kernel p k X n)
    (WittCechTransition.map p k X 0 (n + 1) (Nat.zero_le (n + 1)))
    (WittCechTermKernel.zero_kernel p k X (n + 1))

theorem shortExact (n : ℕ) : (sequence p k X n).ShortExact :=
  SurjectiveScalarComplexSequence.shortExact
    (WittCechTransition.map p k X n (n + 1) (Nat.le_succ n))
    (WittCechTermKernel.surjective p k X n (n + 1) (Nat.le_succ n)) (p : R)
    (WittCechTermKernel.successive_kernel p k X n)
    (WittCechTransition.map p k X 0 (n + 1) (Nat.zero_le (n + 1)))
    (WittCechTermKernel.zero_kernel p k X (n + 1))
    (WittCechTermKernel.surjective p k X 0 (n + 1) (Nat.zero_le (n + 1)))

theorem first (n : ℕ) : (sequence p k X n).X₁ = WittCechTransitionData.complex p k X n := rfl
theorem middle (n : ℕ) : (sequence p k X n).X₂ = WittCechTransitionData.complex p k X (n + 1) := rfl
theorem last (n : ℕ) : (sequence p k X n).X₃ = WittCechTransitionData.complex p k X 0 := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechExactSequence
