import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCoefficientKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransition

/-! # Witt Cech Term Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTermKernel

noncomputable section

/-! Surjectivity and scalar exactness for every degree of the native global Witt Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCoefficientKernel

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

theorem surjective (n m : ℕ) (hnm : n ≤ m) (a : ℕ) :
    Function.Surjective ((WittCechTransition.map p k X n m hnm).f a) :=
  Module.ProductScalarKernel.surjective.{u + 1, u, u + 1} (WittCoefficientKernel.sectionModule p k X m a) (WittCoefficientKernel.sectionModule p k X n a)
    (WittCechTransitionData.coefficient p k X n m hnm a) (WittCoefficientKernel.surjective p k X n m hnm a)

theorem successive_kernel (n a : ℕ) (x : (WittCechTransitionData.complex p k X (n + 1)).X a) :
    (WittCechTransition.map p k X n (n + 1) (Nat.le_succ n)).f a x = 0 ↔ (p : R) • x = 0 :=
  Module.ProductScalarKernel.kernel.{u + 1, u, u + 1} (WittCoefficientKernel.sectionModule p k X (n + 1) a) (WittCoefficientKernel.sectionModule p k X n a)
    (WittCechTransitionData.coefficient p k X n (n + 1) (Nat.le_succ n) a) (p : R)
    (WittCoefficientKernel.successive_kernel p k X n a) x

theorem zero_kernel (n a : ℕ) (x : (WittCechTransitionData.complex p k X n).X a) :
    (WittCechTransition.map p k X 0 n (Nat.zero_le n)).f a x = 0 ↔
      ∃ y : (WittCechTransitionData.complex p k X n).X a, (p : R) • y = x :=
  Module.ProductScalarKernel.scalar_range.{u + 1, u, u + 1} (WittCoefficientKernel.sectionModule p k X n a) (WittCoefficientKernel.sectionModule p k X 0 a)
    (WittCechTransitionData.coefficient p k X 0 n (Nat.zero_le n) a) (p : R)
    (WittCoefficientKernel.zero_kernel p k X n a) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTermKernel
