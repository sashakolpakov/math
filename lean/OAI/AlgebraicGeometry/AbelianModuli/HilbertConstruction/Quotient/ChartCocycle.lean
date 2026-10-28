import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ChartTransitions

/-! # Chart Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient

noncomputable section

/-! Identity and composition coherence for the actual quotient-chart transitions. -/

universe u v w

variable {R : Type u} [Ring R] {U : Type v} {V : Type w}
  [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]

/-- The new quotient projection is the explicitly normalized block formula. -/
theorem Charts.QuotientChart.transition_projection_comp (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V)
    (h : Function.Bijective (c.firstBlock e)) :
    (c.firstBlock e).comp (c.transition e h).projection = c.projection.comp e := by
  change (c.firstBlock e).comp
    (LinearMap.id.coprod (Charts.QuotientChart.ofCoordinates (c.transitionCoordinates e h)).coordinates) = _
  rw [Charts.QuotientChart.coordinates_ofCoordinates]
  exact c.transition_projection e h

/-- The first blocks multiply when two valid changes of coordinates are composed. -/
theorem Charts.QuotientChart.firstBlock_comp (c : Charts.QuotientChart R U V) (e f : U × V →ₗ[R] U × V)
    (h : Function.Bijective (c.firstBlock e)) :
    c.firstBlock (e.comp f) = (c.firstBlock e).comp ((c.transition e h).firstBlock f) := by
  have he := congrArg
    (fun q : U × V →ₗ[R] U => (q.comp f).comp (LinearMap.inl R U V))
    (c.transition_projection_comp e h)
  exact he.symm

/-- Two successive valid coordinate changes give a valid composite change. -/
theorem Charts.QuotientChart.firstBlock_comp_bijective (c : Charts.QuotientChart R U V) (e f : U × V →ₗ[R] U × V)
    (he : Function.Bijective (c.firstBlock e))
    (hf : Function.Bijective ((c.transition e he).firstBlock f)) :
    Function.Bijective (c.firstBlock (e.comp f)) := by
  rw [c.firstBlock_comp e f he]
  exact he.comp hf

/-- Coordinate changes satisfy the cocycle identity as actual quotient submodules. -/
theorem Charts.QuotientChart.transition_comp (c : Charts.QuotientChart R U V) (e f : U × V →ₗ[R] U × V)
    (he : Function.Bijective (c.firstBlock e))
    (hf : Function.Bijective ((c.transition e he).firstBlock f)) :
    (c.transition e he).transition f hf =
      c.transition (e.comp f) (c.firstBlock_comp_bijective e f he hf) := by
  apply Subtype.ext
  change (Charts.QuotientChart.ofCoordinates ((c.transition e he).transitionCoordinates f hf)).val =
    (Charts.QuotientChart.ofCoordinates (c.transitionCoordinates (e.comp f) _)).val
  rw [Charts.QuotientChart.transition_kernel, Charts.QuotientChart.transition_kernel]
  change (Charts.QuotientChart.ofCoordinates (c.transitionCoordinates e he)).val.comap f = c.val.comap (e.comp f)
  rw [Charts.QuotientChart.transition_kernel]
  rfl

/-- The identity ambient map always gives a valid first block. -/
theorem Charts.QuotientChart.firstBlock_id (c : Charts.QuotientChart R U V) : c.firstBlock LinearMap.id = LinearMap.id := by
  simp [Charts.QuotientChart.firstBlock, Charts.QuotientChart.projection]

/-- The identity change of coordinates recovers the original quotient. -/
theorem Charts.QuotientChart.transition_id (c : Charts.QuotientChart R U V) :
    c.transition LinearMap.id (by rw [c.firstBlock_id]; exact Function.bijective_id) = c := by
  apply Subtype.ext
  exact c.transition_kernel LinearMap.id _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient
