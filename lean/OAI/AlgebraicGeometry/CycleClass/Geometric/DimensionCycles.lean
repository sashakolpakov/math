import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Dimension Cycles -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles

noncomputable section

/-!
# Algebraic cycles graded by actual function-field dimension

This module is separate from the earlier specialization-coheight cycle API.
Its grading uses the transcendence degrees of the actual function fields of
an integral projective variety and of the reduced integral closed subscheme
on each irreducible support. It accepts no arbitrary dimension function.

The support is allowed to be singular. These are genuine finite algebraic
cycles, not Betti classes; no cycle-class map or Hodge assertion is assumed.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open scoped BigOperators

universe v

/-- Codimension by the difference of actual function-field dimensions. -/
def dimensionCodimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Z : IrreducibleCloseds V.carrier) : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap -
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap

/-- Actual support dimension and codimension add to the ambient dimension.
The support-dimension inequality removes any truncated-subtraction ambiguity. -/
theorem supportDimension_add_dimensionCodimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Z : IrreducibleCloseds V.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + dimensionCodimension V Z =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  exact Nat.add_sub_of_le (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le Z V.structureMap)

/-- The actual irreducible closed supports in the indicated dimension grading. -/
def DimensionCycleSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  {Z : IrreducibleCloseds V.carrier // dimensionCodimension V Z = p}

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The reduced integral closed scheme on the cycle support. -/
abbrev scheme (Z : DimensionCycleSupport V p) : Scheme := GenericPoint.reducedSupportScheme Z.1

/-- Its actual closed immersion into the projective ambient variety. -/
abbrev inclusion (Z : DimensionCycleSupport V p) : Z.scheme ⟶ V.carrier :=
  GenericPoint.reducedSupportι Z.1

/-- Its induced complex structure morphism. -/
abbrev structureMap (Z : DimensionCycleSupport V p) : Z.scheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  SupportFiniteType.supportStructureMap Z.1 V.structureMap

instance scheme_isIntegral (Z : DimensionCycleSupport V p) : IsIntegral Z.scheme :=
  GenericPoint.reducedSupportScheme_isIntegral Z.1

instance inclusion_isClosedImmersion (Z : DimensionCycleSupport V p) :
    IsClosedImmersion Z.inclusion := GenericPoint.reducedSupportι_isClosedImmersion Z.1

/-- Every support inherits a genuine projective embedding. Smoothness of that
support is neither assumed nor required. -/
def projectivePresentation (Z : DimensionCycleSupport V p) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation Z.scheme Z.structureMap :=
  V.presentation.projective.reducedSupport Z.1

instance structureMap_isProper (Z : DimensionCycleSupport V p) : IsProper Z.structureMap :=
  Z.projectivePresentation.isProper

instance structureMap_locallyOfFiniteType (Z : DimensionCycleSupport V p) :
    LocallyOfFiniteType Z.structureMap := by infer_instance

/-- The indexing condition is literally the difference of the two function-field dimensions. -/
theorem dimension_difference (Z : DimensionCycleSupport V p) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap -
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap = p := Z.2

/-- A degree-`p` support has dimension exactly ambient dimension minus `p`. -/
theorem dimension_add_codimension (Z : DimensionCycleSupport V p) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  simpa only [Z.2] using supportDimension_add_dimensionCodimension V Z.1

/-- The dimension-based codimension never exceeds the ambient dimension. -/
theorem codimension_le_ambient (Z : DimensionCycleSupport V p) :
    p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  rw [← Z.dimension_difference]
  exact Nat.sub_le _ _

/-- There are no supports in degrees greater than the dimension of the variety. -/
theorem isEmpty_of_ambient_lt (h : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap < p) :
    IsEmpty (DimensionCycleSupport V p) :=
  ⟨fun Z => (Nat.not_le_of_lt h) Z.codimension_le_ambient⟩

/-- The unique actual scheme point generic in the irreducible support. -/
def genericPoint (Z : DimensionCycleSupport V p) : V.carrier :=
  irreducibleSetEquivPoints Z.1

/-- The support label really is the closure of the indicated generic point. -/
theorem genericPoint_spec (Z : DimensionCycleSupport V p) :
    IsGenericPoint Z.genericPoint (Z.1 : Set V.carrier) :=
  Z.1.isIrreducible.isGenericPoint_genericPoint Z.1.isClosed

/-- Distinct irreducible supports have distinct generic points. -/
theorem genericPoint_injective :
    Function.Injective (DimensionCycleSupport.genericPoint : DimensionCycleSupport V p → V.carrier) := by
  intro Z W h
  apply Subtype.ext
  exact irreducibleSetEquivPoints.injective h

/-- The coefficient-preserving embedding into the point index used by mathlib. -/
def genericPointEmbedding (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    DimensionCycleSupport V p ↪ V.carrier :=
  ⟨DimensionCycleSupport.genericPoint, genericPoint_injective⟩

/-- The constructed integral support maps its own generic point to this label. -/
theorem inclusion_genericPoint (Z : DimensionCycleSupport V p) :
    Z.inclusion (_root_.genericPoint Z.scheme) = Z.genericPoint :=
  GenericPoint.reducedSupport_genericPoint_eq Z.1

end DimensionCycleSupport

/-- Finite algebraic cycles with the genuine function-field dimension grading. -/
abbrev DimensionCycle (R : Type v) [Zero R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  DimensionCycleSupport V p →₀ R

abbrev IntegralDimensionCycle (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  DimensionCycle ℤ V p

abbrev RationalDimensionCycle (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  DimensionCycle ℚ V p

namespace DimensionCycle

variable {R : Type v} {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- A dimension-graded algebraic cycle above the ambient dimension vanishes. -/
theorem eq_zero_of_ambient_lt [Zero R] (z : DimensionCycle R V p)
    (h : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap < p) : z = 0 := by
  let := DimensionCycleSupport.isEmpty_of_ambient_lt h
  exact Finsupp.ext fun Z => isEmptyElim Z

/-- Forgetting the dimension grade retains every irreducible-support coefficient. -/
def toSupportFinsupp [Zero R] (z : DimensionCycle R V p) :
    IrreducibleCloseds V.carrier →₀ R :=
  Finsupp.embDomain (Function.Embedding.subtype fun Z => dimensionCodimension V Z = p) z

@[simp]
theorem toSupportFinsupp_apply [Zero R] (z : DimensionCycle R V p)
    (Z : DimensionCycleSupport V p) : z.toSupportFinsupp Z.1 = z Z :=
  Finsupp.embDomain_apply_self _ _ _

/-- Extension by zero away from the actual dimension grade. -/
theorem toSupportFinsupp_apply_of_codimension_ne [Zero R] (z : DimensionCycle R V p)
    (Z : IrreducibleCloseds V.carrier) (hZ : dimensionCodimension V Z ≠ p) :
    z.toSupportFinsupp Z = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨W, rfl⟩
  exact hZ W.2

theorem toSupportFinsupp_injective [Zero R] :
    Function.Injective (DimensionCycle.toSupportFinsupp : DimensionCycle R V p →
      IrreducibleCloseds V.carrier →₀ R) :=
  Finsupp.embDomain_injective _

/-- The same cycle in the generic-point index used by mathlib's algebraic cycles. -/
def toPointFinsupp [Zero R] (z : DimensionCycle R V p) : V.carrier →₀ R :=
  Finsupp.embDomain (DimensionCycleSupport.genericPointEmbedding V p) z

@[simp]
theorem toPointFinsupp_apply [Zero R] (z : DimensionCycle R V p)
    (Z : DimensionCycleSupport V p) : z.toPointFinsupp Z.genericPoint = z Z :=
  Finsupp.embDomain_apply_self _ _ _

theorem toPointFinsupp_injective [Zero R] :
    Function.Injective (DimensionCycle.toPointFinsupp : DimensionCycle R V p → V.carrier →₀ R) :=
  Finsupp.embDomain_injective _

/-- These finite cycles determine actual mathlib algebraic cycles with the same
coefficients on the unique generic points of their supports. -/
def toAlgebraicCycle [Zero R] (z : DimensionCycle R V p) : AlgebraicCycle V.carrier R :=
  FiniteSupport.Cycles.finsuppToAlgebraicCycle z.toPointFinsupp

@[simp]
theorem toAlgebraicCycle_apply [Zero R] (z : DimensionCycle R V p)
    (Z : DimensionCycleSupport V p) : z.toAlgebraicCycle Z.genericPoint = z Z :=
  toPointFinsupp_apply z Z

theorem toAlgebraicCycle_injective [Zero R] :
    Function.Injective (DimensionCycle.toAlgebraicCycle : DimensionCycle R V p → AlgebraicCycle V.carrier R) := by
  intro z w h
  apply Finsupp.ext
  intro Z
  have he := congrArg (fun c : AlgebraicCycle V.carrier R => c Z.genericPoint) h
  simpa only [toAlgebraicCycle_apply] using he

/-- Actual irreducible closed supports form the free basis of these cycles. -/
def basis (R : Type v) [Semiring R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Module.Basis (DimensionCycleSupport V p) R (DimensionCycle R V p) :=
  Finsupp.basisSingleOne

@[simp]
theorem basis_apply [Semiring R] (Z : DimensionCycleSupport V p) :
    basis R V p Z = Finsupp.single Z (1 : R) := rfl

/-- Every cycle is its finite linear combination of actual irreducible supports. -/
theorem eq_sum_support [Semiring R] (z : DimensionCycle R V p) :
    z = ∑ Z ∈ z.support, z Z • Finsupp.single Z (1 : R) := by
  classical
  simpa only [Finsupp.sum, Finsupp.smul_single_one] using (Finsupp.sum_single z).symm

/-- The dimension grade is a concrete supported submodule, using the fixed
function-field dimensions above rather than an arbitrary weight function. -/
def supportedSubmodule (R : Type v) [Semiring R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule R (IrreducibleCloseds V.carrier →₀ R) :=
  Finsupp.supported R R {Z | dimensionCodimension V Z = p}

/-- Finite support labels and the concrete supported submodule are equivalent. -/
def equivSupported (R : Type v) [Semiring R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    DimensionCycle R V p ≃ₗ[R] supportedSubmodule R V p :=
  (Finsupp.supportedEquivFinsupp (R := R) {Z | dimensionCodimension V Z = p}).symm

end DimensionCycle

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles
