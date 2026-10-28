import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.PointFlatness
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Closed Fiber Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ClosedFiberFlatness

noncomputable section

/-! For a proper family over a local base, local spectra above the
closed base point suffice to test flatness everywhere. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem proper_closedPoint_maps_to_closedPoint
    (A : CommRingCat.{u}) [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec A) [IsProper f] (x : X) (hx : IsClosed ({x} : Set X)) :
    f x = IsLocalRing.closedPoint A := by
  have hfx : IsClosed ({f x} : Set (Spec A)) := by
    simpa only [Set.image_singleton] using f.isClosedMap {x} hx
  have hc : IsLocalRing.closedPoint A ∈ closure ({f x} : Set (Spec A)) :=
    specializes_iff_mem_closure.mp (IsLocalRing.specializes_closedPoint (f x))
  have he : IsLocalRing.closedPoint A = f x := by
    simpa only [hfx.closure_eq, Set.mem_singleton_iff] using! hc
  exact he.symm

theorem proper_flat_of_closedFiberStalks
    (A : CommRingCat.{u}) [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec A) [IsProper f]
    (h : ∀ x : X, f x = IsLocalRing.closedPoint A → Flat (X.fromSpecStalk x ≫ f)) :
    Flat f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  apply Closed.PointFlatness.flat_of_closed_sourceStalks f
  intro x hx
  exact h x (proper_closedPoint_maps_to_closedPoint A f x hx)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ClosedFiberFlatness
