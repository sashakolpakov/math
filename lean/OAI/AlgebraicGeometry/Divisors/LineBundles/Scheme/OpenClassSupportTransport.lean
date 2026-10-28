import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport

/-! # Open Class Support Transport -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenClassSupportTransport.BundleCycles

noncomputable section

/-! Equal actual local support sets give the same canonical supported class of a fixed graded cycle under the literal support transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (F G : Set U) (h : F = G)
  (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

theorem schemeOpenRestrictedClass_supportTransport (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of U) (congrArg Set.compl h) rfl
      (OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap X U F d p hd (OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle X U F d c)) =
    OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap X U G d p hd (OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle X U G d c) := by
  subst G
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenClassSupportTransport.BundleCycles
