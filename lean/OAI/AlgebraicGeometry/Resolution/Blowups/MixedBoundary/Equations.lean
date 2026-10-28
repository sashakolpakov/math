import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.WithExceptional

/-! # Equations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations.Construction

noncomputable section

/-! Mixed control-zero/control-one equations and their invertible changes on actual Rees charts. -/

universe u v

variable {R : Type u} {ι : Type v} [CommRing R]

theorem blowupChartRatio_mul_left (I : Ideal R) (a z : I) (r : R) :
    ExceptionalIdeal.Construction.blowupChartRatio I a ⟨r * z.val, I.mul_mem_left r z.property⟩ =
      Blowup.Charts.Construction.blowupChartConstants I a r * ExceptionalIdeal.Construction.blowupChartRatio I a z := by
  apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
  change Blowup.Charts.Construction.blowupChartConstants I a a.val *
      ExceptionalIdeal.Construction.blowupChartRatio I a ⟨r * z.val, I.mul_mem_left r z.property⟩ =
    Blowup.Charts.Construction.blowupChartConstants I a a.val * (Blowup.Charts.Construction.blowupChartConstants I a r * ExceptionalIdeal.Construction.blowupChartRatio I a z)
  rw [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio, map_mul,
    ← ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a z]
  ring

/-- The given finite set records precisely which old equations are
divided once. All other old equations are pulled back unchanged. -/
def blowupMixedBoundaryFamily (I : Ideal R) (a : I) (F : Finset ι)
    (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I) : Option ι → Blowup.Charts.Construction.blowupChart I a := by
  classical
  exact fun j => match j with
    | none => Blowup.Charts.Construction.blowupChartConstants I a a.val
    | some i => if h : i ∈ F then ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w i, hw i h⟩
      else Blowup.Charts.Construction.blowupChartConstants I a (w i)

theorem blowupMixedBoundaryFamily_factorization [DecidableEq ι] (I : Ideal R) (a : I) (F : Finset ι)
    (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I) (j : ι) :
    Blowup.Charts.Construction.blowupChartConstants I a (w j) =
      (Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ (if j ∈ F then 1 else 0) *
        blowupMixedBoundaryFamily I a F w hw (some j) := by
  classical
  by_cases hj : j ∈ F
  · rw [blowupMixedBoundaryFamily, dite_eq_left hj, ite_eq_left hj,
      pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val)]
    exact (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a ⟨w j, hw j hj⟩).symm
  · rw [blowupMixedBoundaryFamily, dite_eq_right hj, ite_eq_right hj,
      pow_zero (Blowup.Charts.Construction.blowupChartConstants I a a.val), one_mul (Blowup.Charts.Construction.blowupChartConstants I a (w j))]

/-- Changing original equations by individual factors changes their
actual mixed transforms by the pulled-back factors, preserving the new
exceptional equation. The algebraic identity needs no unit assumption. -/
theorem blowupMixedBoundaryFamily_mul_factors (I : Ideal R) (a : I) (F : Finset ι)
    (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I) (u : ι → R) (j : Option ι) :
    blowupMixedBoundaryFamily I a F (fun i => u i * w i)
        (fun i hi => I.mul_mem_left (u i) (hw i hi)) j =
      (match j with | none => 1 | some i => Blowup.Charts.Construction.blowupChartConstants I a (u i)) *
        blowupMixedBoundaryFamily I a F w hw j := by
  classical
  cases j with
  | none => exact (one_mul (Blowup.Charts.Construction.blowupChartConstants I a a.val)).symm
  | some i =>
      by_cases hi : i ∈ F
      · simp only [blowupMixedBoundaryFamily, dite_eq_left hi]
        exact blowupChartRatio_mul_left I a ⟨w i, hw i hi⟩ (u i)
      · simp only [blowupMixedBoundaryFamily, dite_eq_right hi, map_mul]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations.Construction
