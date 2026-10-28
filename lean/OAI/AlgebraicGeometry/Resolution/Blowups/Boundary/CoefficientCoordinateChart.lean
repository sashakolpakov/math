import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.FixedNormalBoundaryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseCoordinateFiber

/-! # Coefficient Coordinate Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientCoordinateChart.Construction

noncomputable section

/-! Coefficient neighborhoods with one actual coordinate system for the normal and full boundary. -/

universe u v

structure BoundaryCoefficientCoordinateChart (k : Type u) [CommRing k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (J : Ideal R) (n : ℕ) (p : PrimeSpectrum R) where
  chart : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p
  normalIndex : chart.ambientModel.indices
  normal_eq : chart.ambientModel.map (MvPolynomial.X normalIndex) = chart.normal
  normal_unused : ∀ j, chart.ambientModel.coordinate j ≠ some normalIndex

/-- Further refinement gives one actual étale coordinate system that
retains the already chosen normal equation and every original boundary
label, together with the original point and coefficient-ideal data. -/
theorem exists_boundary_coefficient_coordinate_refinement
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} {J : Ideal R} {n : ℕ} {p : PrimeSpectrum R}
    (C : CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p) :
    Nonempty (BoundaryCoefficientCoordinateChart k R w J n p) := by
  obtain ⟨G⟩ := FixedNormalBoundaryOpen.Construction.exists_fixed_normal_boundary_open C.carrier (fun j => C.map (w j))
    C.ambientModel C.derivative C.derivative_tangent C.normal C.derivative_normal C.point
  let B := G.chart
  let N := B.model.transverseCoordinateFiber G.normalIndex G.normal_unused
  have hcoeff : Etale.BoundaryModel.Construction.EtaleBoundaryModel k (B.carrier ⧸ Ideal.span {B.map C.normal}) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {B.map C.normal}) (B.map (C.map (w j)))) := by
    have ht := congrArg (fun z : B.carrier => Etale.BoundaryModel.Construction.EtaleBoundaryModel k (B.carrier ⧸ Ideal.span {z}) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {z}) (B.map (C.map (w j))))) G.normal_eq
    exact ht ▸ N
  exact ⟨{ chart := C.refine B hcoeff
           normalIndex := G.normalIndex
           normal_eq := G.normal_eq
           normal_unused := G.normal_unused }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientCoordinateChart.Construction
