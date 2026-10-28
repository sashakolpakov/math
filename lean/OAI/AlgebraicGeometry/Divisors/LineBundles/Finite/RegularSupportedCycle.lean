import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularPrincipalSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeImagePoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.RationalPointDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.Point

/-! # Regular Supported Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularSupportedCycle.BundleCycles

noncomputable section

/-! The actual full principal pushforward is a global supported cycle in the section intersection, with every source order and residue degree retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤))
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

local instance finiteRegularSupportedTopNonempty : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

local notation "r" => Scheme.germToFunctionField S.left ⊤ (Scheme.Hom.appTop k.left s)

local instance finiteRegularSupportedIdOpen : IsOpenImmersion (𝟙 S : S ⟶ S).left := by
  change IsOpenImmersion (𝟙 S.left)
  infer_instance

local instance finiteRegularSupportedPointFintype : Fintype (PrincipalBoundary.BundleCycles.finitePrincipalPoint S r) :=
  (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r).support.fintypeCoeSort

def finiteRegularSupportedImagePoint (z : PrincipalBoundary.BundleCycles.finitePrincipalPoint S r) :
    LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint N (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n :=
  ⟨PrimeImagePoint.BundleCycles.finitePrimeImagePoint k p hp (𝟙 S) (PrincipalBoundary.BundleCycles.finitePrincipalPrime S r z) n hn, by
    rw [PrimeImagePoint.BundleCycles.finitePrimeImagePoint_support]
    exact RegularPrincipalSupport.BundleCycles.finiteRegularPrincipal_analytic_support k s z⟩

def finiteRegularSupportedCycle : LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle N (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n :=
  ∑ z : PrincipalBoundary.BundleCycles.finitePrincipalPoint S r,
    Finsupp.single (finiteRegularSupportedImagePoint k s p hp n hn z)
      ((S.left.ord r z.val : ℚ) * (k.left.residueDegree z.val : ℚ))

omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteRegularSupportedCycle_points :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion N.hom n
      (LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget N (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n
        (finiteRegularSupportedCycle k s p hp n hn)) =
    CycleClass.Thom.Point.Constructions.pointPushforward k.left (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r) := by
  classical
  have he : (∑ z : PrincipalBoundary.BundleCycles.finitePrincipalPoint S r,
      Finsupp.single z.val (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r z.val)) = RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r := by
    have hsum := Finset.sum_attach (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r).support
      (fun x => Finsupp.single x (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r x))
    have hu : (Finset.univ : Finset (PrincipalBoundary.BundleCycles.finitePrincipalPoint S r)) =
        (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r).support.attach := Finset.univ_eq_attach _
    rw [hu]
    exact hsum.trans (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S.left r).sum_single
  rw [← he]
  simp only [finiteRegularSupportedCycle, LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion,
    map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, CycleClass.Thom.Point.Constructions.pointPushforward_single]
  rfl

omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteRegularSupportedCycle_forget :
    LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget N (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n
      (finiteRegularSupportedCycle k s p hp n hn) =
    GradedOverPushforward.BundleCycles.finiteOverGradedPushforward k n (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n r) := by
  have hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension S.hom = n + 1 := by
    have hS := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension S.hom
    have hN := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension N.hom
    omega
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective N.hom n
  rw [finiteRegularSupportedCycle_points, GradedOverPushforward.BundleCycles.finiteOverGradedPushforward_forget,
    Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor_push S.left S.hom n hdim]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularSupportedCycle.BundleCycles
