import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty

/-! # Reindex -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restrict actual mixed transforms and their center charts to a specified collection of labels. -/

universe u v t

theorem MixedBoundary.Reindex.Construction.blowupMixedBoundaryFamily_reindex
    {R : Type u} [CommRing R] {ι : Type v} {κ : Type t}
    (I : Ideal R) (a : I) (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I)
    (r : κ → ι) (G : Finset κ) (hG : ∀ j, j ∈ G ↔ r j ∈ F) (j : Option κ) :
    MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a G (fun l => w (r l)) (fun l hl => hw (r l) ((hG l).mp hl)) j =
      MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw (j.map r) := by
  classical
  cases j with
  | none => rfl
  | some j =>
      by_cases hj : j ∈ G
      · simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, Option.map_some, dite_eq_left hj, dite_eq_left ((hG j).mp hj)]
      · have hjF : r j ∉ F := fun h => hj ((hG j).mpr h)
        simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, Option.map_some, dite_eq_right hj, dite_eq_right hjF]

def MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.reindex
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {κ : Type t} {w : ι → R} {I : Ideal R} {F : Finset ι} {p : PrimeSpectrum R}
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p)
    (e : κ ↪ ι) (G : Finset κ) (hG : ∀ j, j ∈ G ↔ e j ∈ F) :
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I (fun j => w (e j)) G p where
  chart := C.chart.reindex e
  coordinates := C.coordinates
  center_eq := C.center_eq
  divided_iff := fun j => (hG j).trans (C.divided_iff (e j))

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.reindex
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {κ : Type t} {w : ι → R} {I : Ideal R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F)
    (e : κ ↪ ι) (G : Finset κ) (hG : ∀ j, j ∈ G ↔ e j ∈ F) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I (fun j => w (e j)) G := by
  intro p hp
  obtain ⟨C⟩ := h p hp
  exact ⟨C.reindex e G hG⟩

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.reindex
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {κ : Type t} {w : ι → R}
    (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (e : κ ↪ ι) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j => w (e j)) := by
  intro p
  obtain ⟨C⟩ := h p
  exact ⟨C.reindex e⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
