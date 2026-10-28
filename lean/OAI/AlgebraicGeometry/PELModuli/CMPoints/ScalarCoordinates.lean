import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarQuotientMk
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Scalar Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarCoordinates

noncomputable section

/-! Coordinate reduction identifies the quotient of a free module by
a scalar with the free module over the corresponding quotient ring. -/

variable {R I : Type*} [CommRing R]

def scalarCoordinateMap (a : R) :
    (I → R) →ₗ[R] (I → R ⧸ Ideal.span ({a} : Set R)) :=
  LinearMap.pi (fun i => (Ideal.span ({a} : Set R)).mkQ.comp (LinearMap.proj i))

theorem scalarCoordinateMap_surjective (a : R) : Function.Surjective
    (scalarCoordinateMap (I := I) a) := by
  intro y
  choose x hx using fun i => (Ideal.span ({a} : Set R)).mkQ_surjective (y i)
  exact ⟨x, funext hx⟩

theorem scalarCoordinateMap_ker (a : R) :
    (scalarCoordinateMap (I := I) a).ker = ScalarQuotientMk.scalarMultiples (M := I → R) a := by
  ext x
  constructor
  · intro hx
    have hx' : ∀ i, x i ∈ Ideal.span ({a} : Set R) := fun i =>
      (Submodule.Quotient.mk_eq_zero _).mp (congrFun hx i)
    choose y hy using fun i => Ideal.mem_span_singleton.mp (hx' i)
    exact ⟨y, funext (fun i => (hy i).symm)⟩
  · rintro ⟨y, rfl⟩
    apply funext
    intro i
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y i, rfl⟩

def scalarCoordinateEquiv (a : R) :
    ScalarQuotientMk.ScalarQuotient R (I → R) a ≃ₗ[R] (I → R ⧸ Ideal.span ({a} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (scalarCoordinateMap_ker (I := I) a).symm).trans
    ((scalarCoordinateMap a).quotKerEquivOfSurjective (scalarCoordinateMap_surjective a))

theorem scalarCoordinateEquiv_mk (a : R) (x : I → R) :
    scalarCoordinateEquiv a (Submodule.Quotient.mk x) =
      fun i => Ideal.Quotient.mk (Ideal.span ({a} : Set R)) (x i) := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarCoordinates
