import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrincipalBoundary
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentSection
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SectionDivisorOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection

/-! # Section Common Boundary -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionCommonBoundary.BundleCycles

noncomputable section

/-! Every prime component of a regular section in any actual source chart belongs to the full parent principal divisor. One global finite boundary therefore controls all these charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SectionDivisorOrder.Constructions

variable {S N X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  (k : S ⟶ N) [IsFinite k.left]
  [IsIntegral X.left] [LocallyOfFiniteType X.hom] (a : X ⟶ S) [IsOpenImmersion a.left]

local instance finiteSectionCommonBoundaryLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom
local instance finiteSectionCommonBoundaryTopNonempty : Nonempty (⊤ : X.left.Opens) :=
  ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (s : Γ(X.left, ⊤)) (hs : X.left.germToFunctionField ⊤ s ≠ 0)
  (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X (X.left.basicOpen s))

local notation "r" => OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentSection.BundleCycles.finiteParentRationalFunction a (X.left.germToFunctionField ⊤ s)

include hs in
omit [AlgebraicGeometry.IsNoetherian S.left] in
theorem finiteSectionAmbientPrime_order_ne_zero :
    S.left.ord r (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val ≠ 0 := by
  have ho := CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime_ord a ⟨z.val, z.property.1⟩ r
  change X.left.ord (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap a.left r) z.val = _ at ho
  rw [ParentSection.BundleCycles.finiteParentRationalFunction_pullback] at ho
  exact fun hz => (CycleClass.Thom.Regular.SectionDivisorOrder.Constructions.ord_ne_zero_of_not_mem_basicOpen X.left s hs z.val z.property.1 z.property.2) (ho.trans hz)

def finiteSectionParentDivisorPoint : PrincipalBoundary.BundleCycles.finitePrincipalPoint S r :=
  ⟨(CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val, Finsupp.mem_support_iff.mpr (by
    rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply]
    exact_mod_cast finiteSectionAmbientPrime_order_ne_zero a s hs z)⟩

theorem finiteSectionParentDivisorPoint_prime :
    PrincipalBoundary.BundleCycles.finitePrincipalPrime S r (finiteSectionParentDivisorPoint a s hs z) =
      CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩ := rfl

include hs in
omit [AlgebraicGeometry.IsIntegral N.left] in
theorem finitePrincipalCommonOpen_subset_sectionDivisor :
    (PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen r k : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
      FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) :=
  PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen_subset r k (finiteSectionParentDivisorPoint a s hs z)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionCommonBoundary.BundleCycles
