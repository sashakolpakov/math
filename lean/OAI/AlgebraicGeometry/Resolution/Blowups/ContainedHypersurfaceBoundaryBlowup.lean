import OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainedHypersurfaceCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryAdjoin
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.AdmissiblePreservation

/-! # Contained Hypersurface Boundary Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ContainedHypersurfaceBoundaryBlowup.Construction

noncomputable section

/-! Keep a contained transverse hypersurface and every old boundary label on all blowup charts. -/

universe u v

theorem adjoined_boundary_center_mem
    {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
    (I : Ideal R) (z : R) (hz : z ∈ I) (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I) :
    ∀ j ∈ insert none (F.image some),
      (match j with | none => z | some j => w j) ∈ I := by
  intro j hj
  cases j with
  | none => exact hz
  | some j =>
      have hjF : j ∈ F := by simpa only [Finset.mem_insert, Option.some_ne_none,
        Finset.mem_image, Option.some.injEq, exists_eq_right, false_or] using hj
      exact hw j hjF

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem contained_transverse_hypersurface_preserves_full_blowup_boundary
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (z : R) (hz : z ∈ I) (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (hcenter : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z = 1)
    (a : I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a (insert none (F.image some))
        (fun j : Option ι => match j with | none => z | some j => w j)
        (adjoined_boundary_center_mem I z hz w F hw)) := by
  exact MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup R I
    (fun j : Option ι => match j with | none => z | some j => w j)
    (insert none (F.image some)) (adjoined_boundary_center_mem I z hz w F hw)
    (hboundary.adjoin_transverse_equation z E hE hEz)
    (hcenter.adjoin_contained_hypersurface z hz E hE hEz) a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ContainedHypersurfaceBoundaryBlowup.Construction
