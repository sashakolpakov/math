import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Transformation

/-! # Witt Cech Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransition

noncomputable section

/-! Canonical level reduction is a morphism of the original global Witt frame Čech complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def map (n m : ℕ) (hnm : n ≤ m) : WittCechTransitionData.complex p k X m ⟶ WittCechTransitionData.complex p k X n :=
  FrameCech.Transformation.map.{u + 1, u} (WittFrameFamily.Family.frame p k X m) (WittFrameFamily.Family.frame p k X n)
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (WittCechTransitionData.sections p k X m) (WittCechTransitionData.sections p k X n)
    (WittCechTransitionData.coefficient p k X n m hnm) (WittCechTransitionData.coefficient_naturality p k X n m hnm)

theorem component (n m : ℕ) (hnm : n ≤ m) (a : ℕ) :
    (map p k X n m hnm).f a = WittCechTransitionData.termMap p k X n m hnm a := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransition
