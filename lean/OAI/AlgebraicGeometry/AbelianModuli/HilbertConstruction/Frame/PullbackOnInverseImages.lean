import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameTransitions

/-! # Pullback On Inverse Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a full inverse-image open, pulled-back frame transitions are the actual structural pullbacks of the original regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem Frame.PullbackOnInverseImages.openSectionPullback_full (W : Y.Opens) (r : Γ(Y, W)) :
    Open.SectionPullback.openSectionPullback f W (f ⁻¹ᵁ W) le_rfl r = f.app W r :=
  ConcreteCategory.congr_hom (X.presheaf.map_id (.op (f ⁻¹ᵁ W))) (f.app W r)

theorem OpenFrame.Transitions.OpenFrameTransitions.pullback_value_on_preimage {ι : Type v} {U : ι → Y.Opens}
    (D : OpenFrame.Transitions.OpenFrameTransitions U) (W : Y.Opens) (i j : ι) (hi : W ≤ U i) (hj : W ≤ U j) :
    ((D.pullback f).value (f ⁻¹ᵁ W) i j ((TopologicalSpace.Opens.map f.base).monotone hi)
      ((TopologicalSpace.Opens.map f.base).monotone hj)).val = f.app W (D.value W i j hi hj).val := by
  have he := congrArg Units.val (D.pullbackUnit_eq_on f (f ⁻¹ᵁ W) i j
    ((TopologicalSpace.Opens.map f.base).monotone hi) ((TopologicalSpace.Opens.map f.base).monotone hj)
    W hi hj le_rfl)
  exact he.trans (Frame.PullbackOnInverseImages.openSectionPullback_full f W (D.value W i j hi hj).val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
