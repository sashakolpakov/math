import OAI.AlgebraicGeometry.CycleClass.Thom.GeometricDiagonalEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDiagonalEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler

/-! # Vector Coefficient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.VectorCoefficient.Constructions

noncomputable section

/-! The coefficient in the actual diagonal section-vector formula is
exactly the original geometric Serre-Tor intersection multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GeometricDiagonalEuler.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem intersectionMultiplicity_eq_pairEuler (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier) :
    IntersectionGeometry.intersectionMultiplicity X A B C = GeometricDiagonalEuler.Constructions.supportPairEuler X.carrier A B (IntersectionGeometry.supportPoint C) X.ambientDimension := rfl

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "x" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.genericPoint (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) Z)

theorem diagonal_vector_coefficient
    (hxA : IntersectionGeometry.supportPoint Z.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint Z.val ∈ (B.val : Set V.carrier))
    (rs : List ((T).carrier.presheaf.stalk x))
    (hI : Ideal.ofList rs = (StalkPrimeQuotient.Constructions.kernelPrime (T).carrier (Support.Constructions.diagonalClosedSupport V) x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z)).asIdeal) :
    Local.Euler.Constructions.localCycleEuler T (p + q) x rs V.presentation.ambientDimension (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1) =
      IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val := by
  rw [Local.Euler.Constructions.localCycleEuler, Finsupp.linearCombination_single, one_smul,
    Local.Euler.Constructions.supportEuler_of_mem T (p + q) x rs V.presentation.ambientDimension (LocalIsolation.Constructions.pairedSupport V p q A B)
      (LocalIsolation.Constructions.generic_mem_product V p q A B Z hxA hxB)]
  have h := Local.QuotientEulerEquiv.Constructions.euler_quotients_congr ((T).carrier.presheaf.stalk x) (Ideal.ofList rs)
    (StalkPrimeQuotient.Constructions.kernelPrime (T).carrier (LocalIsolation.Constructions.pairedSupport V p q A B).val x (LocalIsolation.Constructions.generic_mem_product V p q A B Z hxA hxB)).asIdeal
    (StalkPrimeQuotient.Constructions.kernelPrime (T).carrier (Support.Constructions.diagonalClosedSupport V) x (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z)).asIdeal
    (StalkPrimeQuotient.Constructions.kernelPrime (T).carrier (LocalIsolation.Constructions.pairedSupport V p q A B).val x (LocalIsolation.Constructions.generic_mem_product V p q A B Z hxA hxB)).asIdeal
    hI rfl V.presentation.ambientDimension
  have hT := GeometricDiagonalEuler.Constructions.supportPairEuler_eq_quotients (T).carrier (Support.Constructions.diagonalClosedSupport V) (LocalIsolation.Constructions.pairedSupport V p q A B).val x
    (LocalIsolation.Constructions.generic_mem_diagonal V (p + q) Z) (LocalIsolation.Constructions.generic_mem_product V p q A B Z hxA hxB) V.presentation.ambientDimension
  have he := GeometricDiagonalEuler.Constructions.supportPairEuler_diagonal V p q A B Z.genericPoint hxA hxB V.presentation.ambientDimension
  rw [← Ambient.Constructions.diagonalSupport_genericPoint V (p + q) Z] at he
  exact h.trans (hT.symm.trans (he.symm.trans (intersectionMultiplicity_eq_pairEuler V.presentation A.val B.val Z.val).symm))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.VectorCoefficient.Constructions
