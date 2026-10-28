import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.WithExceptional
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.PhaseLeaves

/-! # Unit Denominator Boundary Model -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.UnitDenominatorBoundaryModel.Construction

noncomputable section

/-! Boundary models on actual blowup charts with invertible denominators. -/

universe u v

variable {k R : Type u} {ι : Type v} [CommRing k] [CommRing R] [Algebra k R]
  {w : ι → R}

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- When the original denominator is a unit, the actual coefficient
map is étale, the exceptional equation is invertible, and dividing all
old equations only changes them by a common unit. -/
def unitDenominatorBoundaryModel (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (I : Ideal R) (a : I) (ha : IsUnit a.val) (hw : ∀ j, w j ∈ I) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Blowup.Charts.Construction.blowupChart I a) (Option ι)
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) := by
  let f := Boundary.PhaseLeaves.Construction.blowupChartConstantsAlgHom k I a
  have hf : f.toRingHom.Etale := RingHom.Etale.of_bijective
    (Blowup.Charts.Construction.blowupChartConstants_bijective_of_isUnit I a ha)
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  have hc : IsUnit c := ha.map (Blowup.Charts.Construction.blowupChartConstants I a)
  let v : Blowup.Charts.Construction.blowupChart I a := ↑hc.unit⁻¹
  have hv : IsUnit v := Units.isUnit _
  have he (j : ι) : ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w j, hw j⟩ = v * f (w j) := by
    apply hc.isRegular.left
    change c * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w j, hw j⟩ = c * (v * f (w j))
    rw [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio, ← mul_assoc c v (f (w j)), hc.mul_val_inv,
      one_mul (f (w j))]
    rfl
  have hfamily : Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw =
      (fun j => match j with | none => c | some i => v * f (w i)) := by
    funext j
    cases j with
    | none => rfl
    | some i => exact he i
  rw [hfamily]
  exact ((M.baseChange f hf).mulUnits (fun _ => v) (fun _ => hv)).adjoinUnit c hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.UnitDenominatorBoundaryModel.Construction
