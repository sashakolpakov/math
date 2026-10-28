import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedSupportedLift

/-! # Regular Supported Class Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularSupportedClassRestriction.BundleCycles

noncomputable section

/-! The global supported class of the full regular principal pushforward restricts to the canonical local class of that same full graded cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤))
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

local instance finiteRegularSupportedClassTopNonempty : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

def finiteRegularPrincipalSupportedClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ (2 * (p + 1)) :=
  Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap N (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n (p + 1) hn
    (RegularSupportedCycle.BundleCycles.finiteRegularSupportedCycle k s p hp n hn)

theorem finiteRegularPrincipalSupportedClass_restrict (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
      (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ U (2 * (p + 1)) (finiteRegularPrincipalSupportedClass k s p hp n hn) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U (Subtype.val ⁻¹' RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n (p + 1) hn
      (Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle N U (Subtype.val ⁻¹' RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n
        (GradedOverPushforward.BundleCycles.finiteOverGradedPushforward k n (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n
          (S.left.germToFunctionField ⊤ (k.left.appTop s))))) := by
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
    (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ U (2 * (p + 1))
    (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap N (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n (p + 1) hn
      (RegularSupportedCycle.BundleCycles.finiteRegularSupportedCycle k s p hp n hn)) = _
  rw [Scheme.ClosedSupportedLift.BundleCycles.schemeClosedRelativeClassMap_restrict]
  apply Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap_eq_restrict_of_local_coefficients N U
    (Subtype.val ⁻¹' RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) n (p + 1) hn
  intro D _
  rw [Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_toOpen_forget, RegularSupportedCycle.BundleCycles.finiteRegularSupportedCycle_forget]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularSupportedClassRestriction.BundleCycles
