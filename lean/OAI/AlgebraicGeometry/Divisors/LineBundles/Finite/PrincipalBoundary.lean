import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.GraphDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenPurity

/-! # Principal Boundary -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrincipalBoundary.BundleCycles

noncomputable section

/-! The finite principal divisor determines one actual closed exceptional set. Its codimension is two greater than the parent image, uniformly over all local charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable (S : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral S.left] [AlgebraicGeometry.IsNoetherian S.left]
  (r : S.left.functionField)

abbrev finitePrincipalPoint := {x : S.left // x ∈ (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r).support}

def finitePrincipalPrime (z : finitePrincipalPoint S r) : {x : S.left // Order.coheight x = 1} :=
  ⟨z.val, by
    by_contra hn
    have hz := Finsupp.mem_support_iff.mp z.property
    exact hz ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply S.left r z.val).trans
      ((congrArg (fun n : ℤ => (n : ℚ)) (Scheme.ord_eq_zero_of_coheight_neq_one hn r)).trans Int.cast_zero))⟩

variable {S} [Smooth S.hom] {N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral N.left] [Smooth N.hom]
  (k : S ⟶ N) [IsFinite k.left]

def finitePrincipalBoundary : Closeds N.left :=
  ⟨⋃ z : finitePrincipalPoint S r,
      (FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (finitePrincipalPrime S r z)) : Set N.left),
    isClosed_iUnion_of_finite (fun z => (FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary k
      (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (finitePrincipalPrime S r z))).isClosed)⟩

variable (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

include hp in
theorem finitePrincipalBoundary_codimension (A : IrreducibleCloseds N.left)
    (hA : (A : Set N.left) ⊆ finitePrincipalBoundary r k) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A N.hom + (p + 2) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom := by
  have hη := A.isIrreducible.isGenericPoint_genericPoint A.isClosed
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hA hη.mem)
  have hsub : (A : Set N.left) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (finitePrincipalPrime S r z)) := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hz)
      (FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (finitePrincipalPrime S r z))).isClosed
  have h := FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary_codimension k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (finitePrincipalPrime S r z))
    (p + 1) (FiniteAffine.GraphDimension.BundleCycles.finitePrimeImage_dimension k p hp (finitePrincipalPrime S r z)) A hsub
  simpa only [Nat.add_assoc] using h

def finitePrincipalCommonOpen : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen N (finitePrincipalBoundary r k).compl

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] in
theorem finitePrincipalCommonOpen_subset (z : finitePrincipalPoint S r) :
    (finitePrincipalCommonOpen r k : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
      FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (finitePrincipalPrime S r z)) := by
  intro x hx hz
  exact hx (Set.mem_iUnion.mpr ⟨z, hz⟩)

variable [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]

include hp in
theorem finitePrincipalCommonOpen_relativeRestriction_isIso
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (T : Set U)
    (hT : T ⊆ {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ finitePrincipalBoundary r k}ᶜ) :
    IsIso (CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ finitePrincipalBoundary r k}ᶜ T (2 * (p + 1))) :=
  CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions.open_relativeRestriction_isIso N
    (finitePrincipalBoundary r k) (p + 2) (finitePrincipalBoundary_codimension r k p hp) U T hT
    (2 * (p + 1)) (by omega)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrincipalBoundary.BundleCycles
