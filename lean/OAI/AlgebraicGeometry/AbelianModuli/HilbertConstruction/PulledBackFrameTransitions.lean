import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameUnits

/-! # Pulled Back Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameTransitions.OpenFrameTransitions

noncomputable section

/-! Pullback of an actual regular-function frame cocycle along an arbitrary scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} {ι : Type v} {U : ι → Y.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions.pullbackUnit_self (V : X.Opens) (i : ι) (hi : V ≤ f ⁻¹ᵁ U i) : D.pullbackUnit f V i i hi hi = 1 := by
  unfold OpenFrame.Transitions.OpenFrameTransitions.pullbackUnit
  rw [D.self]
  exact map_one _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions.pullbackUnit_comp (V : X.Opens) (i j k : ι)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) (hk : V ≤ f ⁻¹ᵁ U k) :
    D.pullbackUnit f V i j hi hj * D.pullbackUnit f V j k hj hk = D.pullbackUnit f V i k hi hk := by
  let W := (U i ⊓ U j) ⊓ U k
  have wi : W ≤ U i := inf_le_left.trans inf_le_left
  have wj : W ≤ U j := inf_le_left.trans inf_le_right
  have wk : W ≤ U k := inf_le_right
  have hV : V ≤ f ⁻¹ᵁ W := le_inf (le_inf hi hj) hk
  let φ := Units.map (Open.SectionPullback.openSectionPullback f W V hV).toMonoidHom
  have hij := D.pullbackUnit_eq_on f V i j hi hj W wi wj hV
  have hjk := D.pullbackUnit_eq_on f V j k hj hk W wj wk hV
  have hik := D.pullbackUnit_eq_on f V i k hi hk W wi wk hV
  exact (congrArg₂ (fun a b : Γ(X, V)ˣ => a * b) hij hjk).trans
    ((map_mul φ (D.value W i j wi wj) (D.value W j k wj wk)).symm.trans
      ((congrArg φ (D.comp W i j k wi wj wk)).trans hik.symm))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions.pullback : OpenFrame.Transitions.OpenFrameTransitions (fun i => f ⁻¹ᵁ U i) where
  value := D.pullbackUnit f
  restrict := D.pullbackUnit_restrict f
  self := D.pullbackUnit_self f
  comp := D.pullbackUnit_comp f

theorem pullback_cover (hU : ∀ y : Y, ∃ i, y ∈ U i) (x : X) : ∃ i, x ∈ f ⁻¹ᵁ U i := hU (f x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PulledBackFrameTransitions.OpenFrameTransitions
