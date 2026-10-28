import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum

/-! # Intrinsic Cotangent Pairing -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentPairing.Intrinsic

noncomputable section

/-! The native cotangent coordinate map preserves the actual sum of
local symplectic pairings. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem cotangent_pairing (u v : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    Adelic.DataTheta.standardPairing (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B u) (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B v) =
      ∑ w : Fin A.places, Adelic.DataTheta.standardPairing (u w) (v w) := by
  change (∑ i, (B.realPosition (fun w j => u w (.inl j)) i *
      IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w j => v w (.inr j)) i -
      IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w j => u w (.inr j)) i *
        B.realPosition (fun w j => v w (.inl j)) i)) = _
  rw [Finset.sum_sub_distrib]
  change B.realPosition (fun w j => u w (.inl j)) ⬝ᵥ IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w j => v w (.inr j)) -
    IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w j => u w (.inr j)) ⬝ᵥ B.realPosition (fun w j => v w (.inl j)) = _
  rw [dotProduct_comm (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B _),IntrinsicDualMomentum.Intrinsic.real_momentum_duality,IntrinsicDualMomentum.Intrinsic.real_momentum_duality,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [dotProduct_comm (fun j => v w (.inl j))]
  exact (Finset.sum_sub_distrib _ _).symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentPairing.Intrinsic
