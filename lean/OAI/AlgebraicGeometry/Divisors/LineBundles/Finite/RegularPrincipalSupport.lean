import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrincipalBoundary
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen

/-! # Regular Principal Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularPrincipalSupport.BundleCycles

noncomputable section

/-! The full image of every component of an actual pulled-back regular divisor lies in the parent image and the ambient section zero set, including the omitted boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤))

local instance finiteRegularPrincipalTopNonempty : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

variable (z : PrincipalBoundary.BundleCycles.finitePrincipalPoint S (S.left.germToFunctionField ⊤ (k.left.appTop s)))

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [IsFinite (Over.Hom.left k)] in
theorem finiteRegularPrincipal_source_support :
    (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (PrincipalBoundary.BundleCycles.finitePrincipalPrime S (S.left.germToFunctionField ⊤ (k.left.appTop s)) z) : Set S.left) ⊆
      (S.left.basicOpen (k.left.appTop s) : Set S.left)ᶜ := by
  have hz : z.val ∈ (RegularDivisor.BundleCycles.regularFunctionDivisor S.left (k.left.appTop s)).support := by
    apply Finsupp.mem_support_iff.mpr
    intro h
    exact (Finsupp.mem_support_iff.mp z.property)
      (show (S.left.ord (S.left.germToFunctionField ⊤ (k.left.appTop s)) z.val : ℚ) = 0 from
        (congrArg (fun n : ℤ => (n : ℚ)) h).trans Int.cast_zero)
  exact closure_minimal (Set.singleton_subset_iff.mpr
    (RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset S.left (k.left.appTop s) hz))
    (S.left.basicOpen (k.left.appTop s)).isOpen.isClosed_compl

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] in
theorem finiteRegularPrincipal_image_support :
    (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (PrincipalBoundary.BundleCycles.finitePrincipalPrime S (S.left.germToFunctionField ⊤ (k.left.appTop s)) z)) : Set N.left) ⊆
      (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S) : Set N.left) ∩ (N.left.basicOpen s : Set N.left)ᶜ := by
  rw [CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_eq_image, CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_eq_image]
  rintro _ ⟨x, hx, rfl⟩
  constructor
  · refine ⟨x, ?_, rfl⟩
    change x ∈ closure {genericPoint S.left}
    rw [(genericPoint_spec S.left).def]
    trivial
  · intro h
    apply finiteRegularPrincipal_source_support k s z hx
    have he := Scheme.preimage_basicOpen_top k.left s
    exact (congrArg (fun U : S.left.Opens => x ∈ U) he).mp h

def finiteRegularSectionSupport : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) :=
  Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) ∩ Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s)

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] in
theorem finiteRegularPrincipal_analytic_support :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k
      (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (PrincipalBoundary.BundleCycles.finitePrincipalPrime S (S.left.germToFunctionField ⊤ (k.left.appTop s)) z)))) ⊆
    finiteRegularSectionSupport k s := by
  intro y hy
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range] at hy
  have h := finiteRegularPrincipal_image_support k s z hy
  constructor
  · rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
    exact h.1
  · rw [CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
    change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation y s = 0
    by_contra hn
    exact h.2 ((CycleClass.Thom.GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff N s y).mpr hn)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularPrincipalSupport.BundleCycles
