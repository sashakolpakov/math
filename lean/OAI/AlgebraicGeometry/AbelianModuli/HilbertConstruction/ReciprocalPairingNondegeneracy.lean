import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReciprocalFramePairingValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.SectionContraction

/-! # Reciprocal Pairing Nondegeneracy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual reciprocal-frame pairing detects global sections by contraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal N)
variable (hU : ∀ x : X, ∃ i, x ∈ U i)

theorem CompatibleSheaf.CompatibleSheafFrames.reciprocalPairing_contractLeft_injective :
    Function.Injective (E.reciprocalPairing F hU).contractLeft := by
  intro s t h
  apply M.isSheaf.section_ext
  intro x _
  obtain ⟨i, hi⟩ := hU x
  refine ⟨U i, le_top, hi, ?_⟩
  have hv := congrArg (fun φ : N ⟶ Line.Bundles.structureModule X =>
    φ.app (U i) (F.frame (U i) i le_rfl 1)) h
  rw [Bilinear.Sheaves.SheafBilinearMap.contractLeft_app, Bilinear.Sheaves.SheafBilinearMap.contractLeft_app,
    E.reciprocalPairing_app F hU (U i) i le_rfl,
    E.reciprocalPairing_app F hU (U i) i le_rfl] at hv
  simp only [LinearEquiv.symm_apply_apply, mul_one] at hv
  exact (E.frame (U i) i le_rfl).symm.injective hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
