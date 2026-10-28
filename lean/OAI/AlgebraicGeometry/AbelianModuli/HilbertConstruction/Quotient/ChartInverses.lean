import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ChartCocycle

/-! # Chart Inverses -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient

noncomputable section

/-! Inverse coordinate changes give equivalences on quotient-chart overlaps. -/

universe u v w

variable {R : Type u} [Ring R] {U : Type v} {V : Type w}
  [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]

/-- Pulling the new projection back by the inverse ambient isomorphism applies the inverse first block. -/
theorem Charts.QuotientChart.transition_inverse_projection (c : Charts.QuotientChart R U V) (e : (U × V) ≃ₗ[R] (U × V))
    (h : Function.Bijective (c.firstBlock e.toLinearMap)) :
    (c.transition e.toLinearMap h).projection.comp e.symm.toLinearMap =
      (LinearEquiv.ofBijective (c.firstBlock e.toLinearMap) h).symm.toLinearMap.comp c.projection := by
  let A := LinearEquiv.ofBijective (c.firstBlock e.toLinearMap) h
  apply LinearMap.ext
  intro x
  apply A.injective
  change A ((c.transition e.toLinearMap h).projection (e.symm x)) = A (A.symm (c.projection x))
  rw [A.apply_symm_apply]
  exact (LinearMap.congr_fun (c.transition_projection_comp e.toLinearMap h) (e.symm x)).trans
    (congrArg c.projection (e.apply_symm_apply x))

/-- The first block for the reverse coordinate change is the inverse of the original first block. -/
theorem Charts.QuotientChart.transition_inverse_firstBlock (c : Charts.QuotientChart R U V) (e : (U × V) ≃ₗ[R] (U × V))
    (h : Function.Bijective (c.firstBlock e.toLinearMap)) :
    (c.transition e.toLinearMap h).firstBlock e.symm.toLinearMap =
      (LinearEquiv.ofBijective (c.firstBlock e.toLinearMap) h).symm.toLinearMap := by
  have he := congrArg (fun q : U × V →ₗ[R] U => q.comp (LinearMap.inl R U V))
    (c.transition_inverse_projection e h)
  simpa [Charts.QuotientChart.firstBlock, LinearMap.comp_assoc, Charts.QuotientChart.projection] using he

/-- Every valid coordinate change has a valid reverse change. -/
theorem Charts.QuotientChart.transition_inverse_bijective (c : Charts.QuotientChart R U V) (e : (U × V) ≃ₗ[R] (U × V))
    (h : Function.Bijective (c.firstBlock e.toLinearMap)) :
    Function.Bijective ((c.transition e.toLinearMap h).firstBlock e.symm.toLinearMap) := by
  rw [c.transition_inverse_firstBlock e h]
  exact (LinearEquiv.ofBijective (c.firstBlock e.toLinearMap) h).symm.bijective

/-- The reverse transition recovers the original quotient. -/
theorem Charts.QuotientChart.transition_inverse (c : Charts.QuotientChart R U V) (e : (U × V) ≃ₗ[R] (U × V))
    (h : Function.Bijective (c.firstBlock e.toLinearMap)) :
    (c.transition e.toLinearMap h).transition e.symm.toLinearMap
      (c.transition_inverse_bijective e h) = c := by
  apply Subtype.ext
  change (Charts.QuotientChart.ofCoordinates ((c.transition e.toLinearMap h).transitionCoordinates e.symm.toLinearMap _)).val = _
  rw [Charts.QuotientChart.transition_kernel]
  change (Charts.QuotientChart.ofCoordinates (c.transitionCoordinates e.toLinearMap h)).val.comap e.symm.toLinearMap = _
  rw [Charts.QuotientChart.transition_kernel]
  ext x
  change e (e.symm x) ∈ c.val ↔ x ∈ c.val
  rw [e.apply_symm_apply]

/-- The two descriptions of the same quotient-chart overlap are equivalent. -/
def Charts.QuotientChart.overlapEquiv (e : (U × V) ≃ₗ[R] (U × V)) :
    {c : Charts.QuotientChart R U V // Function.Bijective (c.firstBlock e.toLinearMap)} ≃
      {c : Charts.QuotientChart R U V // Function.Bijective (c.firstBlock e.symm.toLinearMap)} where
  toFun c := ⟨c.val.transition e.toLinearMap c.property, c.val.transition_inverse_bijective e c.property⟩
  invFun c := ⟨c.val.transition e.symm.toLinearMap c.property,
    c.val.transition_inverse_bijective e.symm c.property⟩
  left_inv c := Subtype.ext (c.val.transition_inverse e c.property)
  right_inv c := Subtype.ext (c.val.transition_inverse e.symm c.property)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient
