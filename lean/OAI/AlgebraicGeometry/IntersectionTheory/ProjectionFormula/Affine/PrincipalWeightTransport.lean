import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeight
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportGermOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalWeightDivisorOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Prime

/-! # Principal Weight Transport -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeightTransport

noncomputable section

/-! Affine principal weights agree with the native divisor weights
of the original support and its ambient chart section. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem native (R : Type) [CommRing R] [IsNoetherianRing R]
    (v z : PrimeSpectrum R) (hvz : v.asIdeal ≤ z.asIdeal) (r : R) :
    PrincipalWeight.weight R v r z =
      GlobalParameterSum.Weights.weight (Spec (.of R)) z (StructureSheaf.toStalk R z r)
        (SupportStalk.support R v) := by
  rw [PrincipalWeight.weight, dite_eq_left hvz]
  exact (GlobalWeightDivisorOrder.order (Spec (.of R)) z (StructureSheaf.toStalk R z r)
    (SupportStalk.support R v) (SupportStalk.mem R v z hvz)).symm

theorem chart (X : Scheme) (W : IrreducibleCloseds X) (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)] [IsNoetherianRing Γ(X, U)]
    (z : PrimeSpectrum Γ(X, U))
    (hvz : (ClosedSupportCoordinates.prime (CycleClass.Geometric.GenericPoint.reducedSupportι W) U).asIdeal ≤ z.asIdeal)
    (hzU : hU.fromSpec z ∈ U) (r : Γ(X, U)) :
    PrincipalWeight.weight Γ(X, U)
      (ClosedSupportCoordinates.prime (CycleClass.Geometric.GenericPoint.reducedSupportι W) U) r z =
      GlobalParameterSum.Weights.weight X (hU.fromSpec z)
        (X.presheaf.germ U (hU.fromSpec z) hzU r) W := by
  let v := ClosedSupportCoordinates.prime (CycleClass.Geometric.GenericPoint.reducedSupportι W) U
  let A := SupportStalk.support Γ(X, U) v
  have hA : hU.fromSpec (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint W := by
    rw [SupportStalk.point]
    exact (ClosedSupportCoordinates.point (CycleClass.Geometric.GenericPoint.reducedSupportι W) U hU).trans
      (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W)
  have hzA := SupportStalk.mem Γ(X, U) v z hvz
  have hzW : hU.fromSpec z ∈ (W : Set X) :=
    CoverIsolation.image_subset hU.fromSpec A W hA ⟨z, hzA, rfl⟩
  rw [native Γ(X, U) v z hvz r]
  rw [← ChartGerm.apply X U hU z hzU r]
  exact Open.SupportGermOrder.weight hU.fromSpec A W hA z hzA hzW
    (X.presheaf.germ U (hU.fromSpec z) hzU r)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeightTransport
