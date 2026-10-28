import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransform

/-! # Logarithmic Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LogarithmicTransform.Construction

noncomputable section

/-! Preserve the relative logarithmic invariant for the exact mixed boundary family. -/

variable (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Every permissible controlled blowup preserves the relative
logarithmic bound for the displayed mixed old family and the new
exceptional equation. This is the same family used in the geometric
normal-crossing proofs. -/
theorem blowup_mixed_boundary_preserves_relative_logarithmic_bound
    (I J : Ideal R) (a : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I)
    (m : ℕ) (hJ : J ≤ I ^ m)
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J m = ⊤) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (Equations.Construction.blowupMixedBoundaryFamily I a F w hw)
      (ControlledTransform.Construction.blowupControlledTransform I J m a) m = ⊤ := by
  classical
  let v : ι → Blowup.Charts.Construction.blowupChart I a := fun j => Equations.Construction.blowupMixedBoundaryFamily I a F w hw (some j)
  let e : ι → ℕ := fun j => if j ∈ F then 1 else 0
  have he : ∀ j, Blowup.Charts.Construction.blowupChartConstants I a (w j) =
      (Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ e j * v j :=
    Equations.Construction.blowupMixedBoundaryFamily_factorization I a F w hw
  have h := Relative.LogarithmicTransform.Construction.blowup_preserves_relative_logarithmic_order_bound k I J a w v e he m hJ hbound
  have hfamily : (fun j : Option ι => Option.elim j (Blowup.Charts.Construction.blowupChartConstants I a a.val) v) =
      Equations.Construction.blowupMixedBoundaryFamily I a F w hw := by
    funext j
    cases j <;> rfl
  rw [hfamily] at h
  exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LogarithmicTransform.Construction
