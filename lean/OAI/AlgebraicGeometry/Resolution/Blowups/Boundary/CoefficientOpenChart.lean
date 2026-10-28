import OAI.AlgebraicGeometry.Resolution.Blowups.ActiveModeledBoundaryFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Smooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension

/-! # Coefficient Open Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenChart.Construction

noncomputable section

/-! A pointed coefficient neighborhood with the entire boundary and actual hypersurface retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

/-- Data for coefficient induction at an original prime: an actual
open immersion, a normal equation and derivative, and explicit models
for the full boundary both upstairs and on the coefficient hypersurface. -/
structure BoundaryCoefficientOpenChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (J : Ideal R) (n : ℕ) (p : PrimeSpectrum R) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  point : PrimeSpectrum carrier
  point_over : PrimeSpectrum.comap map.toRingHom point = p
  normal : carrier
  normal_mem : normal ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map map.toRingHom) n
  normal_mem_point : normal ∈ point.asIdeal
  derivative : Derivation k carrier carrier
  derivative_normal : derivative normal = 1
  derivative_tangent : derivative ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => map (w j))
  ambientModel : Etale.BoundaryModel.Construction.EtaleBoundaryModel k carrier ι (fun j => map (w j))
  coefficientModel : Etale.BoundaryModel.Construction.EtaleBoundaryModel k (carrier ⧸ Ideal.span {normal}) ι
    (fun j => Ideal.Quotient.mk (Ideal.span {normal}) (map (w j)))

attribute [instance] BoundaryCoefficientOpenChart.algebra BoundaryCoefficientOpenChart.isOpenImmersion

variable {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
  {ι : Type v} {w : ι → R} {J : Ideal R} {n : ℕ} {p : PrimeSpectrum R}

theorem BoundaryCoefficientOpenChart.coefficient_smooth (C : BoundaryCoefficientOpenChart k R w J n p) :
    Algebra.Smooth k (C.carrier ⧸ Ideal.span {C.normal}) := C.coefficientModel.smooth

/-- The actual coefficient space is lower-dimensional than the original
ambient dimension bound, using the displayed normal derivative. -/
theorem BoundaryCoefficientOpenChart.coefficient_dimension [CharZero k]
    (C : BoundaryCoefficientOpenChart k R w J n p) (d : ℕ)
    (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (C.carrier ⧸ Ideal.span {C.normal}) ≤ d := by
  let : Algebra.Smooth k C.carrier := C.ambientModel.smooth
  let : IsNoetherianRing C.carrier := Algebra.FiniteType.isNoetherianRing k C.carrier
  let : Algebra ℚ C.carrier := ((algebraMap k C.carrier).comp (algebraMap ℚ k)).toAlgebra
  exact Coordinate.HypersurfaceDimension.Construction.coordinateHypersurface_dimension_induction C.derivative C.normal C.derivative_normal d
    ((Affine.OpenDimension.Construction.ringKrullDim_le_of_spec_openImmersion C.map.toRingHom).trans hd)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenChart.Construction
