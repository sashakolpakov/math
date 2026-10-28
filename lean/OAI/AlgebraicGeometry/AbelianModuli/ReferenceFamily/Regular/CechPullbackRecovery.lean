import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CocyclePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.FrameIsoRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameCoordinates

/-! # Cech Pullback Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechPullbackRecovery

noncomputable section

/-! Pulling back the constructed cocycle line recovers the actual line
constructed from the pulled-back regular cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem isOpenCover_preimage {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type}
    (U : I → Y.Opens) (hU : IsOpenCover U) : IsOpenCover (fun i => f ⁻¹ᵁ U i) := by
  apply IsOpenCover.mk
  rw [← f.preimage_iSup, hU.iSup_eq_top, f.preimage_top]

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type} (U : I → Y.Opens)
    (r : TransitionCocycle.RegularTransitionCoefficients U) (hr : TransitionCocycle.RegularTransitionCocycle U r)

include hr in
theorem regularCechLineModule_pullback_iso (hU : IsOpenCover U) :
    Nonempty ((Scheme.Modules.pullback f).obj (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) ≅
      Cech.LineModule.cechLineModule (fun i => f ⁻¹ᵁ U i)
        (CechGenerator.regularCechCoefficients (fun i => f ⁻¹ᵁ U i) (CocyclePullback.regularTransitionPullback f U r))) := by
  let M := Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)
  let V := fun i => f ⁻¹ᵁ U i
  let q := CocyclePullback.regularTransitionPullback f U r
  let hq := CocyclePullback.regularTransitionPullback_cocycle f U r hr
  let s := fun i => Local.PullbackFrames.pullbackLocalFrame f M (CechFrame.regularCechNativeFrame U r hr i)
  let t := CechFrame.regularCechNativeFrame V q hq
  apply Local.FrameIsoRecovery.exists_iso_of_localFrame_transitions s t (isOpenCover_preimage f U hU) (fun _ => rfl)
  intro i j
  have h₁ := (Pullback.FrameCoordinates.pullbackLocalFrame_transition f M (CechFrame.regularCechNativeFrame U r hr i)
    (CechFrame.regularCechNativeFrame U r hr j) (U i ⊓ U j) inf_le_left inf_le_right).symm
  have h₂ := congrArg (Units.map (f.app (U i ⊓ U j)).hom.toMonoidHom)
    (CechFrame.regularCechNativeFrame_transition U r hr i j (U i ⊓ U j) inf_le_left inf_le_right)
  have h₃ := (CocyclePullback.regularTransitionPullback_on f U r j i (U i ⊓ U j) inf_le_right inf_le_left).symm
  exact h₁.trans (h₂.trans (h₃.trans
    (CechFrame.regularCechNativeFrame_transition V q hq i j (V i ⊓ V j) inf_le_left inf_le_right).symm))

theorem regularCechLineBundle_pullback_iso (hU : IsOpenCover U) :
    Nonempty ((HilbertConstruction.Line.Bundles.LineBundle.pullback f (CechFrame.regularCechLineBundle U r hr hU)).sheaf ≅
      (CechFrame.regularCechLineBundle (fun i => f ⁻¹ᵁ U i) (CocyclePullback.regularTransitionPullback f U r)
        (CocyclePullback.regularTransitionPullback_cocycle f U r hr) (isOpenCover_preimage f U hU)).sheaf) :=
  regularCechLineModule_pullback_iso f U r hr hU

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechPullbackRecovery
