import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.LocalSpectra
import Mathlib.Topology.Separation.Basic

/-! # Point Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.PointFlatness

noncomputable section

/-! Flatness can be checked on local spectra at closed source points
when the source is quasi-compact. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem flat_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    Flat (Spec.map (X.presheaf.stalkSpecializes h)) := by
  have : Flat (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y) := by
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Presentations.Flat.LocalSpectra.flat_fromSpecStalk X x
  exact Presentations.Flat.LocalSpectra.flat_of_comp_mono _ (X.fromSpecStalk y)

theorem flat_of_sourceStalk_composites {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, Flat (X.fromSpecStalk x ≫ f)) : Flat f := by
  apply Flat.of_stalkMap
  intro x
  have : Flat (Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk (f x)) := by
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact h x
  have hf : Flat (Spec.map (f.stalkMap x)) := Presentations.Flat.LocalSpectra.flat_of_comp_mono _ (Y.fromSpecStalk (f x))
  exact Flat.SpecMap_iff.mp hf

theorem flat_of_closed_sourceStalks {X Y : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Y) (h : ∀ x : X, IsClosed ({x} : Set X) → Flat (X.fromSpecStalk x ≫ f)) :
    Flat f := by
  apply flat_of_sourceStalk_composites f
  intro x
  obtain ⟨y, hy, hyc⟩ := isClosed_closure.exists_closed_singleton
    (Set.singleton_nonempty x).closure
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have : Flat (Spec.map (X.presheaf.stalkSpecializes hxy)) := flat_stalkSpecializes hxy
  have : Flat (X.fromSpecStalk y ≫ f) := h y hyc
  have hc : Flat (Spec.map (X.presheaf.stalkSpecializes hxy) ≫ (X.fromSpecStalk y ≫ f)) := inferInstance
  simpa only [← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk] using hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.PointFlatness
