import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalFrame

/-! # Normalized Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.NormalizedFrame

noncomputable section

/-! The weighted native negative-line frame in orthonormal coordinates.
The change of base coordinate is holomorphic scalar division. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {k : Type} [Field k]

def normalizeWeightedPhase (r c : k) (w : (Fin 3 → k) × (Fin 3 → k)) :
    (Fin 3 → k) × (Fin 3 → k) :=
  ((Matrix.diagonal ![c, c, c * r]).mulVec w.1,
   (Matrix.diagonal ![-c, -c, c * r]).mulVec w.2)

def lineAnnihilatorFrame (z : Fin 2 → k) (u : Fin 3 → k) :
    (Fin 3 → k) × (Fin 3 → k) :=
  (u 0 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z, u 1 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector z 0 + u 2 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector z 1)

theorem weightedFrame_normalized (r c : k) (hr : r ≠ 0)
    (z : Fin 2 → k) (u : Fin 3 → k) :
    normalizeWeightedPhase r c (UnitaryFrameAction.weightedFrame (-(r ^ 2)) z u) =
      lineAnnihilatorFrame (fun i => z i / r)
        ((Matrix.diagonal ![c * r, -c, -c]).mulVec u) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [normalizeWeightedPhase, UnitaryFrameAction.weightedFrame, lineAnnihilatorFrame,
      UnitaryFrameAction.weightedAnnihilator, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector, Matrix.mulVec_diagonal] <;>
    field_simp

theorem normalizeWeightedPhase_injective (r c : k) (hr : r ≠ 0) (hc : c ≠ 0) :
    Function.Injective (normalizeWeightedPhase r c) := by
  intro x y h
  have hleft := congrArg Prod.fst h
  have hright := congrArg Prod.snd h
  apply Prod.ext <;> funext i
  · have hi := congrFun hleft i
    simp only [normalizeWeightedPhase, Matrix.mulVec_diagonal] at hi
    apply mul_left_cancel₀ _ hi
    fin_cases i <;> simp [hc, hr]
  · have hi := congrFun hright i
    simp only [normalizeWeightedPhase, Matrix.mulVec_diagonal] at hi
    apply mul_left_cancel₀ _ hi
    fin_cases i <;> simp [hc, hr]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.NormalizedFrame
