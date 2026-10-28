import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport

/-! # Supported Class Transport -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedClassTransport.BundleCycles

noncomputable section

/-! Canonical classes of the same actual finite cycle respect proved support and codimension equalities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

theorem schemeClosedRestrictedClass_identityMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (F G : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hF : F = G)
    (hm : Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) Gᶜ Fᶜ)
    (d p : ℕ) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hm (2 * p)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X F d p hp (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X F d c)) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X G d p hp (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X G d c) := by
  subst G
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (2 * p)) _

theorem schemeClosedRestrictedClass_supportDegreeTransport (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (F G : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hF : F = G)
    (d p q : ℕ) (hpq : p = q) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hq : d + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (congrArg Set.compl hF)
      (congrArg (fun n => 2 * n) hpq)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X F d p hp (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X F d c)) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X G d q hq (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X G d c) := by
  subst G
  subst q
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedClassTransport.BundleCycles
