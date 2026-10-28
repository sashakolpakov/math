import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizedDivisorFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationHeight
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber

/-! # Normalization Divisor Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual principal divisors push forward from finite normalization

The proof uses the entire normalization fiber, with canonical residue
field degrees and the actual pullback of rational functions. It applies
to singular integral supports and includes poles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

/-- At every divisor point, pushforward from the constructed global
normalization reproduces the original scheme's actual integer order. -/
theorem normalizationPrincipalDivisor_coefficient (x : X) (hx : coheight x = 1)
    (g : X.functionField) (hg : g ≠ 0) :
    letI := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g)) x =
        (X.ord g x : ℚ) := by
  let := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let x' : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨x'⟩
  let := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
  rw [IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_coeff_of_fiber_cover
    (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x') (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) x
    (NormalizationStalkMap.BundleCycles.normalizationStalkMap_injective X U hU x')
    (NormalizationFiber.BundleCycles.normalizationStalkMap_residueDegree X U hU x')
    (NormalizationFiber.BundleCycles.normalizationStalkMap_covers_fiber X U hU x'),
    NormalizedDivisorFiber.BundleCycles.normalizedPrincipalPointDivisor_comap X f U hU x' hx g,
    NormalizationStalkMap.BundleCycles.normalizationStalkMap_comp]
  rw [NormalizedDivisorFiber.BundleCycles.normalizedLocal_principalDivisor_toScheme X f x hx g hg,
    Finsupp.single_eq_same]

/-- The actual finite principal divisor on the global normalization pushes
to the original principal divisor, including all its coefficients. -/
theorem normalizationPrincipalDivisor_pushforward (g : X.functionField) (hg : g ≠ 0) :
    letI := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g)) =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g := by
  let := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  ext x
  by_cases hx : coheight x = 1
  · exact normalizationPrincipalDivisor_coefficient X f x hx g hg
  · rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hx, Int.cast_zero]
    apply IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_apply_eq_zero
    intro y hy hxy
    have hyone : coheight y = 1 := by
      by_contra hn
      apply hy
      rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn,
        Int.cast_zero]
    apply hx
    rw [← hxy, NormalizationHeight.BundleCycles.normalizationMap_coheight X f y, hyone]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward.BundleCycles
