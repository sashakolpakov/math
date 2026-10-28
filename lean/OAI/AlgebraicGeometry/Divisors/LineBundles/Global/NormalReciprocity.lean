import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkResidueFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueSupportCoheight

/-! # Normal Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalReciprocity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete geometric residue reciprocity on normal finite-type schemes

Every nonzero contribution is supported at coheight two. At each such
point the full boundary restricts to the actual local surface boundary,
which has been proved zero for all pairs of rational functions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open scoped Classical

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (hNormal : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include f

theorem normalResidueBoundaryCycle_zero (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h = 0 := by
  ext y
  by_cases hy : coheight y = 2
  · exact StalkResidueFamily.BundleCycles.normalResidueBoundary_coefficient_zero_of_coheight_two X hNormal y g h hy
  · unfold Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro p _
    by_contra hz
    exact hy (ResidueSupportCoheight.BundleCycles.primeSupport_divisor_coheight_two f p (Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight X g h p)
      (Normal.PointResidue.BundleCycles.normalResidueFunctionOnSupport X hNormal g h p) y hz)

theorem normalGradedResidueBoundaryCycle_zero (d : ℕ)
    (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2) (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalGradedResidueBoundaryCycle X hNormal f d g h = 0 := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [Normal.PointResidue.BundleCycles.normalGradedResidueBoundaryCycle_push X hNormal f d hX g h,
    normalResidueBoundaryCycle_zero X hNormal f g h, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalReciprocity.BundleCycles
