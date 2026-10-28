import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrimeClassComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.RationalPointDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalPointSum

/-! # Graded Principal Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedPrincipalClass.BundleCycles

noncomputable section

/-! On a smooth integral complex scheme, its full rational principal
divisor has zero canonical cycle class in the actual dimension grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (d : ℕ) (hd : d + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

def schemePrimeDimensionPoint (z : {x : X.left // Order.coheight x = 1}) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d :=
  ⟨z.val, by
    have h := PrimeClassComparison.BundleCycles.schemePrimeSupport_codimension X z
    exact Nat.add_right_cancel (h.trans hd.symm)⟩

variable {g : X.left.functionField} (D : CycleClass.Thom.RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

local instance : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem gradedRationalPointDivisor_eq_primeSum :
    Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor X.left X.hom d g =
      ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain,
        Finsupp.single (schemePrimeDimensionPoint X d hd ⟨z.val, z.property.1⟩) (X.left.ord g z.val : ℚ) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective X.hom d
  rw [Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor_push X.left X.hom d hd.symm, map_sum]
  refine (CycleClass.Thom.Scheme.PrincipalPointSum.Constructions.principalPointDivisor_eq_sum X D).trans
    (Finset.sum_congr rfl ?_)
  intro z _
  exact (Finsupp.mapDomain_single (f := Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding X.hom d)
    (a := schemePrimeDimensionPoint X d hd ⟨z.val, z.property.1⟩) (b := (X.left.ord g z.val : ℚ))).symm

include D in
theorem schemeGradedCycleClass_principal_zero (hg : g ≠ 0) :
    GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d 1 hd (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor X.left X.hom d g) = 0 := by
  rw [gradedRationalPointDivisor_eq_primeSum X d hd D, map_sum]
  have h := CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class.principal_absolute_sum_zero X D hg
  refine (Finset.sum_congr rfl ?_).trans h
  intro z _
  rw [GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_single]
  exact congrArg (fun a => (X.left.ord g z.val : ℚ) • a) (PrimeClassComparison.BundleCycles.schemeCycleClass_prime X ⟨z.val, z.property.1⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedPrincipalClass.BundleCycles
