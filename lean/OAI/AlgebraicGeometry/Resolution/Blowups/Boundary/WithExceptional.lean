import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FamilyTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart

/-! # With Exceptional -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.WithExceptional.Construction

noncomputable section

/-! Keep the new exceptional equation alongside the fixed labels of old boundaries. -/

universe u v

variable {R S : Type u} {ι : Type v} [CommRing R] [CommRing S]

def blowupBoundaryWithExceptional (I : Ideal R) (a : I) (w : ι → R)
    (hw : ∀ j, w j ∈ I) : Option ι → Blowup.Charts.Construction.blowupChart I a
  | none => Blowup.Charts.Construction.blowupChartConstants I a a.val
  | some j => ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w j, hw j⟩

/-- Actual base change preserves each retained old equation and the
new exceptional equation, with the same labels. -/
theorem blowupBoundaryWithExceptional_map (I : Ideal R) (a : I) (w : ι → R)
    (hw : ∀ j, w j ∈ I) (φ : R →+* S) (j : Option ι) :
    ChartLift.Construction.blowupChartMap I φ a (blowupBoundaryWithExceptional I a w hw j) =
      blowupBoundaryWithExceptional (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩
        (fun l => φ (w l)) (fun l => Ideal.mem_map_of_mem _ (hw l)) j := by
  cases j with
  | none => exact ChartLift.Construction.blowupChartMap_constants I φ a a.val
  | some j => exact Etale.BlowupChart.Construction.blowupChartMap_ratio I φ a ⟨w j, hw j⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.WithExceptional.Construction
