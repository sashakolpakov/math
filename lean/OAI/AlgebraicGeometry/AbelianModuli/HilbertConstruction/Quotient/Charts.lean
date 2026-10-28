import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.Charts

noncomputable section

/-! Explicit coordinates for quotient-module charts used in Grassmannian parameter spaces. -/

universe u v w

variable (R : Type u) [Ring R] (U : Type v) (V : Type w)
  [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]

/-- A quotient lies in this chart when the first summand maps isomorphically onto it. -/
def QuotientChart :=
  {N : Submodule R (U × V) // Function.Bijective (N.mkQ.comp (LinearMap.inl R U V))}

namespace QuotientChart

variable {R U V}

/-- The first summand provides the canonical frame of a quotient in the chart. -/
def frame (c : QuotientChart R U V) : U ≃ₗ[R] ((U × V) ⧸ c.val) :=
  LinearEquiv.ofBijective (c.val.mkQ.comp (LinearMap.inl R U V)) c.property

@[simp]
theorem frame_apply (c : QuotientChart R U V) (u : U) :
    c.frame u = c.val.mkQ (u, 0) := rfl

/-- The second summand is expressed in the frame supplied by the first summand. -/
def coordinates (c : QuotientChart R U V) : V →ₗ[R] U :=
  c.frame.symm.toLinearMap.comp (c.val.mkQ.comp (LinearMap.inr R U V))

/-- Every quotient class is the sum of its two coordinate contributions. -/
theorem frame_symm_mkQ (c : QuotientChart R U V) (u : U) (v : V) :
    c.frame.symm (c.val.mkQ (u, v)) = u + c.coordinates v := by
  have he : (u, v) = (u, (0 : V)) + ((0 : U), v) := by simp
  rw [he, map_add, map_add]
  change c.frame.symm (c.frame u) + c.coordinates v = _
  rw [c.frame.symm_apply_apply]

/-- A linear map specifies a quotient chart point by the kernel of its split projection. -/
def ofCoordinates (L : V →ₗ[R] U) : QuotientChart R U V := by
  let f : U × V →ₗ[R] U := LinearMap.id.coprod L
  have hf : Function.Surjective f := fun u => ⟨(u, 0), by simp [f]⟩
  let e := f.quotKerEquivOfSurjective hf
  have he (u : U) : e (f.ker.mkQ (u, 0)) = u := by simp [e, f]
  refine ⟨f.ker, ?_, ?_⟩
  · intro u v huv
    exact (he u).symm.trans ((congrArg e huv).trans (he v))
  · intro q
    refine ⟨e q, e.injective ?_⟩
    exact he (e q)

/-- The kernel of a quotient in the chart is determined by its coordinate map. -/
theorem kernel_eq (c : QuotientChart R U V) :
    c.val = (LinearMap.id.coprod c.coordinates).ker := by
  ext x
  change x ∈ c.val ↔ x.1 + c.coordinates x.2 = 0
  rw [← Submodule.Quotient.mk_eq_zero]
  exact (c.frame.symm.map_eq_zero_iff).symm.trans
    (Iff.of_eq (congrArg (fun u : U => u = 0) (c.frame_symm_mkQ x.1 x.2)))

/-- Reconstructing a quotient from its coordinates recovers the original submodule. -/
theorem ofCoordinates_coordinates (c : QuotientChart R U V) :
    ofCoordinates c.coordinates = c := by
  apply Subtype.ext
  exact c.kernel_eq.symm

/-- The coordinates of a split-projection kernel are the prescribed linear map. -/
theorem coordinates_ofCoordinates (L : V →ₗ[R] U) :
    (ofCoordinates L).coordinates = L := by
  ext v
  let c := ofCoordinates L
  apply c.frame.injective
  change c.frame (c.frame.symm (c.val.mkQ (0, v))) = c.frame (L v)
  rw [c.frame.apply_symm_apply, frame_apply]
  apply (LinearMap.quotKerEquivOfSurjective
    (LinearMap.id.coprod L) (fun u => ⟨(u, 0), by simp⟩)).injective
  change (LinearMap.id.coprod L) (0, v) = (LinearMap.id.coprod L) (L v, 0)
  simp

/-- Quotients in a fixed chart are parametrized exactly by linear maps between the two summands. -/
def coordinateEquiv : QuotientChart R U V ≃ (V →ₗ[R] U) where
  toFun := QuotientChart.coordinates
  invFun := ofCoordinates
  left_inv := ofCoordinates_coordinates
  right_inv := coordinates_ofCoordinates

end QuotientChart

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.Charts
