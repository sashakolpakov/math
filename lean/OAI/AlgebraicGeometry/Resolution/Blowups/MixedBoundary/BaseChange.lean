import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.BaseChange.Construction

noncomputable section

/-! The same mixed boundary equations and labels commute with actual blowup base change. -/

universe u v

theorem blowupMixedBoundaryFamily_map {R S : Type u} {ι : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) (a : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I)
    (φ : R →+* S) (j : Option ι) :
    ChartLift.Construction.blowupChartMap I φ a (Equations.Construction.blowupMixedBoundaryFamily I a F w hw j) =
      Equations.Construction.blowupMixedBoundaryFamily (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩ F
        (fun l => φ (w l)) (fun l hl => Ideal.mem_map_of_mem φ (hw l hl)) j := by
  classical
  cases j with
  | none => exact ChartLift.Construction.blowupChartMap_constants I φ a a.val
  | some j =>
      by_cases hj : j ∈ F
      · simp only [Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left hj]
        exact Etale.BlowupChart.Construction.blowupChartMap_ratio I φ a ⟨w j, hw j hj⟩
      · simp only [Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hj]
        exact ChartLift.Construction.blowupChartMap_constants I φ a (w j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.BaseChange.Construction
