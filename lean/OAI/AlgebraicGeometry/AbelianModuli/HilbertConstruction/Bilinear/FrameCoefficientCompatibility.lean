import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameCoefficientTuples
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.TransitionEquations

/-! # Frame Coefficient Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameCoefficientCompatibility

noncomputable section

/-! Coefficients of a bilinear pairing against reciprocal frames satisfy the original frame transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M Q : X.Modules} (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal Q)
variable (β : Sheaves.SheafBilinearMap M Q (Line.Bundles.structureModule X))

theorem pairingFrameTuple_compatible (s : Γ(M, ⊤)) :
    Frame.TransitionEquations.FrameCompatible D (FrameCoefficientTuples.pairingFrameTupleMap F β s) := by
  intro i j
  let V := U i ⊓ U j
  change X.presheaf.map (homOfLE (show V ≤ U i from inf_le_left)).op
      (FrameCoefficientTuples.pairingFrameCoefficient F β s i) =
    (D.value V i j inf_le_left inf_le_right).val *
      X.presheaf.map (homOfLE (show V ≤ U j from inf_le_right)).op
        (FrameCoefficientTuples.pairingFrameCoefficient F β s j)
  rw [FrameCoefficientTuples.pairingFrameCoefficient_restrict, FrameCoefficientTuples.pairingFrameCoefficient_restrict]
  have hf := F.change V j i inf_le_right inf_le_left 1
  change F.frame V j inf_le_right ((D.value V i j inf_le_left inf_le_right).val * 1) =
    F.frame V i inf_le_left 1 at hf
  rw [mul_one] at hf
  rw [← hf]
  have hv : F.frame V j inf_le_right (D.value V i j inf_le_left inf_le_right).val =
      (D.value V i j inf_le_left inf_le_right).val • F.frame V j inf_le_right 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (F.frame V j inf_le_right).map_smul (D.value V i j inf_le_left inf_le_right).val (1 : Γ(X, V))
  rw [hv, LinearMap.map_smul]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameCoefficientCompatibility
