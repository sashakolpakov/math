import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalTuples
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.TransitionEquations

/-! # Global Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalCompatibility

noncomputable section

/-! Global sections of the frame presheaf are exactly the compatible regular-function tuples on its covering opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameGlobalTupleEquiv_compatible (x : SectionModules.OpenFrameLocalTuple U ⊤) :
    x ∈ SectionModules.openFrameSectionModule U D ⊤ ↔ Frame.TransitionEquations.FrameCompatible D (GlobalTuples.openFrameGlobalTupleEquiv U x) := by
  rw [SectionModules.openFrameSectionModule_mem_iff]
  change (∀ i j, _) ↔ ∀ i j, Frame.TransitionEquations.FrameTransitionEquation D i j (U i ⊓ U j)
    inf_le_left inf_le_right (GlobalTuples.openFrameGlobalTupleEquiv U x i) (GlobalTuples.openFrameGlobalTupleEquiv U x j)
  apply forall₂_congr
  intro i j
  let Q := ((⊤ : X.Opens) ⊓ U i) ⊓ U j
  let W := U i ⊓ U j
  have a : W ≤ Q := le_inf (le_inf le_top inf_le_left) inf_le_right
  have qj : Q ≤ (⊤ : X.Opens) ⊓ U j := le_inf le_top inf_le_right
  have hi := (Relative.OpenFunctionUnits.openFunction_restriction_comp (le_inf le_top (le_refl (U i)))
    (show W ≤ U i from inf_le_left) (x i)).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show Q ≤ (⊤ : X.Opens) ⊓ U i from inf_le_left) a (x i)).symm
  have hj := (Relative.OpenFunctionUnits.openFunction_restriction_comp (le_inf le_top (le_refl (U j)))
    (show W ≤ U j from inf_le_right) (x j)).trans (Relative.OpenFunctionUnits.openFunction_restriction_comp qj a (x j)).symm
  have ht := D.restrict Q W a i j (inf_le_left.trans inf_le_right) inf_le_right
  have hm := (congrArg₂ (fun r s : Γ(X, W) => r * s) ht.symm hj).trans
    ((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).symm
  have hinj := (LocalFreeness.openFunctionRestriction_bijective_of_eq a (by ext z; simp [W, Q])).injective
  exact ((congrArg₂ Eq hi hm).to_iff.trans hinj.eq_iff).symm

def openFrameGlobalCompatibleModule : Submodule Γ(X, ⊤) (GlobalTuples.OpenFrameGlobalTuple U) :=
  (SectionModules.openFrameSectionModule U D ⊤).map (GlobalTuples.openFrameGlobalTupleEquiv U).toLinearMap

theorem openFrameGlobalCompatibleModule_mem (x : GlobalTuples.OpenFrameGlobalTuple U) :
    x ∈ openFrameGlobalCompatibleModule D ↔ Frame.TransitionEquations.FrameCompatible D x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (openFrameGlobalTupleEquiv_compatible D y).mp hy
  · intro hx
    refine ⟨(GlobalTuples.openFrameGlobalTupleEquiv U).symm x, ?_, (GlobalTuples.openFrameGlobalTupleEquiv U).apply_symm_apply x⟩
    exact (openFrameGlobalTupleEquiv_compatible D _).mpr
      ((congrArg (Frame.TransitionEquations.FrameCompatible D) ((GlobalTuples.openFrameGlobalTupleEquiv U).apply_symm_apply x)).mpr hx)

def openFrameGlobalSectionEquiv :
    SectionModules.openFrameSectionModule U D ⊤ ≃ₗ[Γ(X, ⊤)] openFrameGlobalCompatibleModule D :=
  (GlobalTuples.openFrameGlobalTupleEquiv U).submoduleMap (SectionModules.openFrameSectionModule U D ⊤)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalCompatibility
