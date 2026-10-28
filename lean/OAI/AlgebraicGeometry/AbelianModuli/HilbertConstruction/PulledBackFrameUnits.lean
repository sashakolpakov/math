import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

/-! # Pulled Back Frame Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pull back frame transition units to arbitrary common subopens of the inverse-image cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} {ι : Type v} {U : ι → Y.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

def OpenFrame.Transitions.OpenFrameTransitions.pullbackUnit (V : X.Opens) (i j : ι) (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) : Γ(X, V)ˣ :=
  Units.map (Open.SectionPullback.openSectionPullback f (U i ⊓ U j) V (le_inf hi hj)).toMonoidHom
    (D.value (U i ⊓ U j) i j inf_le_left inf_le_right)

theorem OpenFrame.Transitions.OpenFrameTransitions.pullbackUnit_eq_on (V : X.Opens) (i j : ι)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) (W : Y.Opens)
    (wi : W ≤ U i) (wj : W ≤ U j) (hV : V ≤ f ⁻¹ᵁ W) :
    D.pullbackUnit f V i j hi hj =
      Units.map (Open.SectionPullback.openSectionPullback f W V hV).toMonoidHom (D.value W i j wi wj) := by
  apply Units.ext
  have he := Open.SectionPullback.openSectionPullback_restrict_source f (U i ⊓ U j) W (le_inf wi wj) V hV
    (D.value (U i ⊓ U j) i j inf_le_left inf_le_right).val
  exact he.trans (congrArg (Open.SectionPullback.openSectionPullback f W V hV)
    (D.restrict (U i ⊓ U j) W (le_inf wi wj) i j inf_le_left inf_le_right))

theorem OpenFrame.Transitions.OpenFrameTransitions.pullbackUnit_restrict (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) :
    X.presheaf.map (homOfLE h).op (D.pullbackUnit f V i j hi hj).val =
      (D.pullbackUnit f W i j (h.trans hi) (h.trans hj)).val :=
  Open.SectionPullback.openSectionPullback_restrict_target f (U i ⊓ U j) V W (le_inf hi hj) h _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
