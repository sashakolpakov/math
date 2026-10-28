import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SectionDivisorOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen

/-! # Section Common Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionCommonBoundary.Constructions

noncomputable section

/-! The existing global finite boundary controls every divisor of a
regular section on a normalization open. Nonzero local orders place
these divisors in the original global divisor indexing set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SectionDivisorOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]

local instance : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (s : Γ(X.left, ⊤)) (hs : X.left.germToFunctionField ⊤ s ≠ 0)

local notation "r" => X.left.germToFunctionField ⊤ s
local notation "t" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions.originalFunction V W a r
local notation "ht" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions.originalFunction_ne_zero V W a r hs

variable (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X (X.left.basicOpen s))

include hs in
theorem ambientPrime_not_mem_normalizedUnit :
    (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val ∉ (PrincipalBoundary.Constructions.normalizedUnitRepresentative V W t ht).domain := by
  intro hz
  have ho := Open.PrimeSupport.Constructions.ambientPrime_ord a ⟨z.val, z.property.1⟩ (PrincipalBoundary.Constructions.normalizedFunction V W t)
  rw [OpenFunctionField.Constructions.originalFunction_pullback] at ho
  have hn := Regular.SectionDivisorOrder.Constructions.ord_ne_zero_of_not_mem_basicOpen X.left s hs z.val z.property.1 z.property.2
  apply hn
  exact ho.trans ((PrincipalBoundary.Constructions.normalizedUnitRepresentative V W t ht).ord_eq_zero _ hz)

def sectionGlobalDivisorPoint : Principal.Constructions.DivisorPoint V W t ht :=
  ⟨(Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val,
    (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).property,
    ambientPrime_not_mem_normalizedUnit V W a s hs z⟩

include hs in
theorem commonOpen_subset_sectionDivisor :
    (PrincipalZero.Constructions.BoundaryUnion.commonOpen V W t ht : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩) :=
  PrincipalZero.Constructions.BoundaryUnion.commonOpen_subset_divisor V W t ht (sectionGlobalDivisorPoint V W a s hs z)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionCommonBoundary.Constructions
