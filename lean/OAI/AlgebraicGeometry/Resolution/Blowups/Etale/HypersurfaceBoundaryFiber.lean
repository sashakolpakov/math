import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations

/-! # Hypersurface Boundary Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale

noncomputable section

/-! Retained boundary models on the actual transverse coefficient hypersurface. -/

universe u v

variable {k A R : Type u} {ι : Type v} [CommRing k] [CommRing A] [CommRing R]
  [Algebra k A] [Algebra k R] [Algebra A R] [IsScalarTower k A R]
  [Algebra (Polynomial A) R] [IsScalarTower A (Polynomial A) R]
  [Algebra.Etale (Polynomial A) R] {w : ι → A}

/-- Restricting the retained coefficient equations to the actual
zero fiber preserves their model over the original ground ring. -/
def BoundaryModel.Construction.EtaleBoundaryModel.hypersurfaceFiber (M : BoundaryModel.Construction.EtaleBoundaryModel k A ι w) :
    BoundaryModel.Construction.EtaleBoundaryModel k (HypersurfaceRetraction.Construction.etaleCoordinateFiber A R) ι
      (fun j => algebraMap A (HypersurfaceRetraction.Construction.etaleCoordinateFiber A R) (w j)) := by
  let f : A →ₐ[k] HypersurfaceRetraction.Construction.etaleCoordinateFiber A R := IsScalarTower.toAlgHom k A _
  exact M.baseChange f (RingHom.etale_algebraMap.mpr inferInstance)

/-- Ambient unit factors restrict to units on the coefficient
hypersurface. They need not come from the retained coordinate ring. -/
def BoundaryModel.Construction.EtaleBoundaryModel.hypersurfaceFiberWithUnits (M : BoundaryModel.Construction.EtaleBoundaryModel k A ι w)
    (u : ι → R) (hu : ∀ j, IsUnit (u j)) :
    BoundaryModel.Construction.EtaleBoundaryModel k (HypersurfaceRetraction.Construction.etaleCoordinateFiber A R) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap (Polynomial A) R Polynomial.X})
        (u j * algebraMap A R (w j))) := by
  let H := HypersurfaceRetraction.Construction.etaleCoordinateFiber A R
  let f := Ideal.Quotient.mk (Ideal.span {algebraMap (Polynomial A) R Polynomial.X})
  have he : (fun j => f (u j * algebraMap A R (w j))) =
      (fun j => f (u j) * algebraMap A H (w j)) := by
    funext j
    rw [map_mul]
    rfl
  rw [he]
  exact (M.hypersurfaceFiber (R := R)).mulUnits (fun j => f (u j)) (fun j => (hu j).map f)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale
