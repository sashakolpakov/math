import OAI.AlgebraicGeometry.Resolution.Blowups.UnitDenominatorBoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations

/-! # Unit Denominator Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.UnitDenominatorBoundary.Construction

noncomputable section

/-! Preserve the full mixed boundary on any actual unit-denominator blowup chart. -/

universe u v

variable {k R : Type u} {ι : Type v} [CommRing k] [CommRing R] [Algebra k R]
  {w : ι → R}

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def mixedUnitDenominatorBoundaryModel (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (I : Ideal R) (a : I) (ha : IsUnit a.val) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Blowup.Charts.Construction.blowupChart I a) (Option ι) (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw) := by
  classical
  let f := Boundary.PhaseLeaves.Construction.blowupChartConstantsAlgHom k I a
  have hf : f.toRingHom.Etale := RingHom.Etale.of_bijective (Blowup.Charts.Construction.blowupChartConstants_bijective_of_isUnit I a ha)
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  have hc : IsUnit c := ha.map (Blowup.Charts.Construction.blowupChartConstants I a)
  let v : Blowup.Charts.Construction.blowupChart I a := ↑hc.unit⁻¹
  let u (j : ι) : Blowup.Charts.Construction.blowupChart I a := if j ∈ F then v else 1
  have hu (j : ι) : IsUnit (u j) := by
    by_cases hj : j ∈ F
    · simpa only [u, ite_eq_left hj] using (Units.isUnit (hc.unit⁻¹))
    · simp only [u, ite_eq_right hj, isUnit_one]
  have he (j : ι) (hj : j ∈ F) : ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w j, hw j hj⟩ = v * f (w j) := by
    apply hc.isRegular.left
    change c * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w j, hw j hj⟩ = c * (v * f (w j))
    rw [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio, ← mul_assoc c v (f (w j)), hc.mul_val_inv, one_mul (f (w j))]
    rfl
  have hfamily : MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw =
      (fun j => match j with | none => c | some i => u i * f (w i)) := by
    funext j
    cases j with
    | none => rfl
    | some i =>
        by_cases hi : i ∈ F
        · simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left hi, u, ite_eq_left hi]
          exact he i hi
        · simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hi, u, ite_eq_right hi]
          exact (one_mul (f (w i))).symm
  rw [hfamily]
  exact ((M.baseChange f hf).mulUnits u hu).adjoinUnit c hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.UnitDenominatorBoundary.Construction
