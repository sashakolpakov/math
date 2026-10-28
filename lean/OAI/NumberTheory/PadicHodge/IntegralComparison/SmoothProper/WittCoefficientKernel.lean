import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleScalarKernel

/-! # Witt Coefficient Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCoefficientKernel

noncomputable section

/-! The original large coefficient section maps are surjective and have their native scalar kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family
  WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev sectionModule (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :=
  (WittCechTransitionData.sections p k X n).obj (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t))

theorem surjective (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    Function.Surjective (WittCechTransitionData.coefficient p k X n m hnm a t) := by
  intro x
  obtain ⟨y, hy⟩ := WittTupleReduction.surjective p k X n m hnm a t x.down
  exact ⟨ULift.up y, ULift.ext _ _ hy⟩

theorem quotient_kernel (n m : ℕ) (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)
    (x : sectionModule p k X m a t) :
    WittCechTransitionData.coefficient p k X n m hnm a t x = 0 ↔ ∃ y : sectionModule p k X m a t, (p ^ (n + 1) : ℕ) • y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (WittTupleScalarKernel.quotient_kernel p k X n m hnm a t x.down).mp
      (congrArg ULift.down hx)
    exact ⟨ULift.up y, ULift.ext _ _ hy⟩
  · rintro ⟨y, hy⟩
    apply ULift.ext
    exact (WittTupleScalarKernel.quotient_kernel p k X n m hnm a t x.down).mpr
      ⟨y.down, congrArg ULift.down hy⟩

theorem scalar_kernel (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) (x : sectionModule p k X n a t) :
    (p : ℕ) • x = 0 ↔ ∃ y : sectionModule p k X n a t, (p ^ n : ℕ) • y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (WittTupleScalarKernel.scalar_kernel p k X n a t x.down).mp
      (congrArg ULift.down hx)
    exact ⟨ULift.up y, ULift.ext _ _ hy⟩
  · rintro ⟨y, hy⟩
    apply ULift.ext
    exact (WittTupleScalarKernel.scalar_kernel p k X n a t x.down).mpr
      ⟨y.down, congrArg ULift.down hy⟩

theorem successive_kernel (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) (x : sectionModule p k X (n + 1) a t) :
    WittCechTransitionData.coefficient p k X n (n + 1) (Nat.le_succ n) a t x = 0 ↔
      (p : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) • x = 0 := by
  rw [Nat.cast_smul_eq_nsmul]
  exact (quotient_kernel p k X n (n + 1) (Nat.le_succ n) a t x).trans
    (scalar_kernel p k X (n + 1) a t x).symm

theorem zero_kernel (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) (x : sectionModule p k X n a t) :
    WittCechTransitionData.coefficient p k X 0 n (Nat.zero_le n) a t x = 0 ↔
      ∃ y : sectionModule p k X n a t, (p : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) • y = x := by
  simpa only [zero_add, pow_one, Nat.cast_smul_eq_nsmul] using
    quotient_kernel p k X 0 n (Nat.zero_le n) a t x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCoefficientKernel
