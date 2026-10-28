import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.LocalSmoothness

/-! # Named Boundary Intersection Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary-intersection chart geometry for a fixed named center ideal and denominator. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.blowup_named_intersection
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R] {ι : Type v}
    {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (I : Ideal R) (C : Finset ι) (hI : I = Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C)
    (i : C) (d : I) (hd : d.val = w i.val) (hw : ∀ j ∈ C, w j ∈ I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I d)) (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d C w hw) := by
  subst I
  have he : d = Boundary.Schedule.Construction.boundaryIntersectionGenerator w C i := Subtype.ext hd
  subst d
  exact h.blowup_intersection C i

theorem Boundary.Schedule.Construction.BoundaryFacesCover.blowup_named_intersection
    {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
    {w : ι → R} {L : List (Finset ι)} (h : Boundary.Schedule.Construction.BoundaryFacesCover w L)
    (I : Ideal R) (C : Finset ι) (hI : I = Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C)
    (i : C) (d : I) (hd : d.val = w i.val) (hw : ∀ j ∈ C, w j ∈ I) :
    Boundary.Schedule.Construction.BoundaryFacesCover (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d C w hw) (Boundary.MonomialSchedule.Construction.boundaryScheduleFaces C L) := by
  subst I
  have he : d = Boundary.Schedule.Construction.boundaryIntersectionGenerator w C i := Subtype.ext hd
  subst d
  exact h.blowup_intersection C i

end

end OAI.AlgebraicGeometry.Resolution.Blowups
