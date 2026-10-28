import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseFrameTransitions

/-! # Coefficient Pair Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoefficientPairCompatibility

noncomputable section

/-! Pairwise coefficients with the positive transition factors give compatible morphism coefficients for the reciprocal frame cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U)
variable {N : X.Modules} (t : ∀ i, Γ(N, U i))

theorem frameMorphismCompatible_reciprocal_of_pairwise
    (ht : ∀ i j,
      N.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (t i) =
        (D.value (U i ⊓ U j) i j inf_le_left inf_le_right).val •
          N.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (t j)) :
    Sheaf.FrameCoefficientMaps.FrameMorphismCompatible (D := D.reciprocal) t := by
  intro V i j hi hj
  have hv := congrArg (N.presheaf.map (homOfLE (le_inf hi hj)).op) (ht i j)
  rw [N.map_smul, D.restrict] at hv
  simp only [← N.presheaf.map_comp_apply] at hv
  change N.presheaf.map (homOfLE hi).op (t i) =
    (D.value V i j hi hj).val • N.presheaf.map (homOfLE hj).op (t j) at hv
  rw [D.reciprocal_value, hv, smul_smul]
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoefficientPairCompatibility
