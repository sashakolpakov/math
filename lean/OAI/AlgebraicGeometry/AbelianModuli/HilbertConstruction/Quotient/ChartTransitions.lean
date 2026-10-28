import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.Charts

/-! # Chart Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient

noncomputable section

/-! Explicit coordinate changes between quotient-module charts. -/

universe u v w

variable {R : Type u} [Ring R] {U : Type v} {V : Type w}
  [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]

/-- Normalize the quotient map using the existing frame. -/
def Charts.QuotientChart.projection (c : Charts.QuotientChart R U V) : U × V →ₗ[R] U :=
  LinearMap.id.coprod c.coordinates

/-- The first block of a change of ambient coordinates. -/
def Charts.QuotientChart.firstBlock (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V) : U →ₗ[R] U :=
  (c.projection.comp e).comp (LinearMap.inl R U V)

/-- The second block of a change of ambient coordinates. -/
def Charts.QuotientChart.secondBlock (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V) : V →ₗ[R] U :=
  (c.projection.comp e).comp (LinearMap.inr R U V)

/-- On the overlap where the first block is invertible, the new coordinates are `A⁻¹B`. -/
def Charts.QuotientChart.transitionCoordinates (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V)
    (h : Function.Bijective (c.firstBlock e)) : V →ₗ[R] U :=
  (LinearEquiv.ofBijective (c.firstBlock e) h).symm.toLinearMap.comp (c.secondBlock e)

/-- Renormalizing the new projection by its first block recovers the original quotient map. -/
theorem Charts.QuotientChart.transition_projection (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V)
    (h : Function.Bijective (c.firstBlock e)) :
    (LinearEquiv.ofBijective (c.firstBlock e) h).toLinearMap.comp
      (LinearMap.id.coprod (c.transitionCoordinates e h)) = c.projection.comp e := by
  let A := LinearEquiv.ofBijective (c.firstBlock e) h
  apply LinearMap.ext
  rintro ⟨u, v⟩
  change A (u + A.symm (c.secondBlock e v)) = (c.projection.comp e) (u, v)
  rw [map_add, A.apply_symm_apply]
  change (c.projection.comp e) (u, 0) + (c.projection.comp e) (0, v) =
    (c.projection.comp e) (u, v)
  rw [← map_add]
  congr 1
  simp

/-- The quotient in the new coordinates has exactly the inverse-image defining submodule. -/
theorem Charts.QuotientChart.transition_kernel (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V)
    (h : Function.Bijective (c.firstBlock e)) :
    (Charts.QuotientChart.ofCoordinates (c.transitionCoordinates e h)).val = c.val.comap e := by
  change (LinearMap.id.coprod (c.transitionCoordinates e h)).ker = c.val.comap e
  have hk := congrArg LinearMap.ker (c.transition_projection e h)
  rw [LinearEquiv.ker_comp] at hk
  exact hk.trans (congrArg (fun N => N.comap e) c.kernel_eq.symm)

/-- The actual quotient-chart point in the new ambient coordinates. -/
def Charts.QuotientChart.transition (c : Charts.QuotientChart R U V) (e : U × V →ₗ[R] U × V)
    (h : Function.Bijective (c.firstBlock e)) : Charts.QuotientChart R U V :=
  Charts.QuotientChart.ofCoordinates (c.transitionCoordinates e h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient
