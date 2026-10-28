import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support
import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.EquationIsolation

/-! # Local Isolation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions

noncomputable section

/-! At the diagonal image of an original proper-intersection component,
actual local equations of the geometric diagonal meet the original
reduced product-support module only at the closed stalk point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Proper.EquationIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

abbrev pairedSupport (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) :=
  Integral.ProductSupport.Constructions.integralProductSupport V V (Ambient.Constructions.productVariety V V) (Ambient.Constructions.first V V) (Ambient.Constructions.second V V) (Ambient.Constructions.productLimit V V) p q A B

theorem generic_mem_diagonal (d : ℕ) (C : Geometric.DimensionCycles.DimensionCycleSupport V d) :
    IntersectionGeometry.supportPoint (Ambient.Constructions.diagonalSupport V d C).val ∈ (Support.Constructions.diagonalClosedSupport V : Set (Ambient.Constructions.productVariety V V).carrier) := by
  rw [Support.Constructions.diagonalClosedSupport_coe]
  exact ⟨C.genericPoint, (Ambient.Constructions.diagonalSupport_genericPoint V d C).symm⟩

theorem generic_mem_product (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
    (hxA : IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ (B.val : Set V.carrier)) :
    IntersectionGeometry.supportPoint (Ambient.Constructions.diagonalSupport V (p + q) C).val ∈
      ((pairedSupport V p q A B).val : Set (Ambient.Constructions.productVariety V V).carrier) := by
  have h : (Ambient.Constructions.diagonal V).left C.genericPoint ∈
      ((pairedSupport V p q A B).val : Set (Ambient.Constructions.productVariety V V).carrier) := by
    have he := congrArg (fun S : Set V.carrier => C.genericPoint ∈ S) (Ambient.Constructions.diagonal_product_preimage V p q A B)
    exact he.mpr ⟨hxA, hxB⟩
  change (Ambient.Constructions.diagonalSupport V (p + q) C).genericPoint ∈
    ((pairedSupport V p q A B).val : Set (Ambient.Constructions.productVariety V V).carrier)
  exact (Ambient.Constructions.diagonalSupport_genericPoint V (p + q) C).symm ▸ h

abbrev diagonalStalk (d : ℕ) (C : Geometric.DimensionCycles.DimensionCycleSupport V d) :=
  (Ambient.Constructions.productVariety V V).carrier.presheaf.stalk (Ambient.Constructions.diagonalSupport V d C).genericPoint

variable (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  (hxA : IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier))
  (hxB : IntersectionGeometry.supportPoint C.val ∈ (B.val : Set V.carrier))

local notation "T" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.productVariety V V
local notation "Z" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) C
local notation "x" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.genericPoint (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions.diagonalSupport V (p + q) C)
local notation "R" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions.diagonalStalk V (p + q) C

theorem diagonal_equations_isolated
    (hproper : ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V D)
    (rs : List R)
    (hI : Ideal.ofList rs = (StalkPrimeQuotient.Constructions.kernelPrime (T).carrier (Support.Constructions.diagonalClosedSupport V) x (generic_mem_diagonal V (p + q) C)).asIdeal) :
    PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩
      Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing (T).carrier (pairedSupport V p q A B).val x
        (generic_mem_product V p q A B C hxA hxB)) ⊆ {IsLocalRing.closedPoint R} :=
  Proper.EquationIsolation.Constructions.equations_isolated T ((p + q) + V.complexDimension) (Support.Constructions.diagonalClosedSupport V) (pairedSupport V p q A B).val
    (Support.Constructions.diagonal_product_dimension_bound V p q A B hproper) Z (generic_mem_diagonal V (p + q) C)
    (generic_mem_product V p q A B C hxA hxB) rs hI

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions
