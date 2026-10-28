import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFiber

/-! # Normalization Fiber Connected -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationFiberConnected.Construction

noncomputable section

/-! Transfer actual connected fibers from the normalization map when its finite factor is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsIso f.fromNormalization]

/-- The actual fiber has the same underlying space as the corresponding fiber of the first
normalization map when the second normalization map is an isomorphism. -/
def normalizationFiberHomeomorph (y : Y) :
    f.fiber y ≃ₜ f.toNormalization.fiber ((inv f.fromNormalization) y) :=
  (f.fiberHomeo y).trans ((Homeomorph.setCongr (by
    ext x
    change f x = y ↔ f.toNormalization x = (inv f.fromNormalization) y
    have he : Function.Bijective f.fromNormalization :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso f.fromNormalization))).bijective
    constructor
    · intro hx
      apply he.injective
      change (f.toNormalization ≫ f.fromNormalization) x =
        ((inv f.fromNormalization) ≫ f.fromNormalization) y
      rw [Scheme.Hom.toNormalization_fromNormalization, IsIso.inv_hom_id]
      exact hx
    · intro hx
      have hh := congrArg f.fromNormalization hx
      change (f.toNormalization ≫ f.fromNormalization) x =
        ((inv f.fromNormalization) ≫ f.fromNormalization) y at hh
      rw [Scheme.Hom.toNormalization_fromNormalization, IsIso.inv_hom_id] at hh
      exact hh)).trans
        (f.toNormalization.fiberHomeo ((inv f.fromNormalization) y)).symm)

/-- Actual normalized-fiber connectedness descends through an isomorphic normalization factor. -/
theorem fiber_connected_of_normalization
    (h : ∀ n, ConnectedSpace (f.toNormalization.fiber n)) (y : Y) : ConnectedSpace (f.fiber y) := by
  have := h ((inv f.fromNormalization) y)
  exact (normalizationFiberHomeomorph f y).connectedSpace_iff.mpr inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationFiberConnected.Construction
