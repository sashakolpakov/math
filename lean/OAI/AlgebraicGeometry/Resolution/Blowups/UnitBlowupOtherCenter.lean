import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterUnitOperations
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterEtaleBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.UnitDenominatorBoundary

/-! # Unit Blowup Other Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A unit-denominator blowup preserves the common coordinates of another center. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.unitDenominatorBlowup
    {k : Type u} [CommRing k] (R : CommRingCat.{u}) [Algebra k R]
    (K L : Ideal R) (a : K) (ha : IsUnit a.val) {ι : Type v} (w : ι → R)
    (F G : Finset ι) (hw : ∀ j ∈ F, w j ∈ K) (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R L w G) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k (.of (Blowup.Charts.Construction.blowupChart K a)) (L.map (Blowup.Charts.Construction.blowupChartConstants K a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily K a F w hw) (G.map Function.Embedding.some) := by
  classical
  let f := Boundary.PhaseLeaves.Construction.blowupChartConstantsAlgHom k K a
  have hf : f.toRingHom.Etale := RingHom.Etale.of_bijective (Blowup.Charts.Construction.blowupChartConstants_bijective_of_isUnit K a ha)
  let c := Blowup.Charts.Construction.blowupChartConstants K a a.val
  have hc : IsUnit c := ha.map (Blowup.Charts.Construction.blowupChartConstants K a)
  let v : Blowup.Charts.Construction.blowupChart K a := ↑hc.unit⁻¹
  let u (j : ι) : Blowup.Charts.Construction.blowupChart K a := if j ∈ F then v else 1
  have hu (j : ι) : IsUnit (u j) := by
    by_cases hj : j ∈ F
    · simpa only [u, ite_eq_left hj] using (Units.isUnit (hc.unit⁻¹))
    · simp only [u, ite_eq_right hj, isUnit_one]
  have he (j : ι) (hj : j ∈ F) : ExceptionalIdeal.Construction.blowupChartRatio K a ⟨w j, hw j hj⟩ = v * f (w j) := by
    apply hc.isRegular.left
    change c * ExceptionalIdeal.Construction.blowupChartRatio K a ⟨w j, hw j hj⟩ = c * (v * f (w j))
    rw [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio, ← mul_assoc c v (f (w j)), hc.mul_val_inv, one_mul (f (w j))]
    rfl
  have hfamily : MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily K a F w hw =
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
  exact ((h.etale_baseChange (S := .of (Blowup.Charts.Construction.blowupChart K a)) f hf).mulUnits u hu).adjoinUnit c hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups
