import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DoubleHyperplane

/-! # Hyperplane Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneIntersection.BundleCycles

noncomputable section

/-! The first two coordinate hyperplanes intersect in the
actual smaller symmetric projective spectrum, in a Cartesian square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem symmetricHyperplanes_isPullback (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    IsPullback (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R M) (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R M)
      (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M)) (DoubleHyperplane.BundleCycles.symmetricSecondHyperplane R M) := by
  let f := LinearMap.snd R R (R × M)
  let i := SplitHyperplane.BundleCycles.splitHyperplaneQuotient (DoubleHyperplane.BundleCycles.augmentedCoordinateSwap R M)
  let q := LinearMap.snd R R M
  have hf : Function.Surjective f := fun m => ⟨(0, m), rfl⟩
  have hi : Function.Surjective i := SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective (DoubleHyperplane.BundleCycles.augmentedCoordinateSwap R M)
  have hq : Function.Surjective q := fun m => ⟨(0, m), rfl⟩
  have hlinear : q.comp f = q.comp i := by
    apply LinearMap.ext
    intro z
    rfl
  have h : (GradedMap.BundleCycles.symmetricGradedMap q).comp (GradedMap.BundleCycles.symmetricGradedMap f) =
      (GradedMap.BundleCycles.symmetricGradedMap q).comp (GradedMap.BundleCycles.symmetricGradedMap i) :=
    (GradedMap.BundleCycles.symmetricGradedMap_comp f q).trans ((congrArg GradedMap.BundleCycles.symmetricGradedMap hlinear).trans
      (GradedMap.BundleCycles.symmetricGradedMap_comp i q).symm)
  have hk : RingHom.ker (GradedMap.BundleCycles.symmetricGradedMap q).toRingHom =
      Ideal.span {GradedMap.BundleCycles.symmetricGradedMap f (SplitHyperplane.BundleCycles.splitHyperplaneEquation (DoubleHyperplane.BundleCycles.augmentedCoordinateSwap R M))} :=
    (SymmetricInfinity.Kernel.BundleCycles.symmetricInfinity_kernel R M).trans
      (congrArg (fun a => Ideal.span {a}) (DoubleHyperplane.BundleCycles.symmetricSecondHyperplane_equation_image R M).symm)
  exact Projective.PrincipalPullback.BundleCycles.projectivePrincipal_isPullback (GradedMap.BundleCycles.symmetricGradedMap f) (GradedMap.BundleCycles.symmetricGradedMap i)
    (GradedMap.BundleCycles.symmetricGradedMap q) (GradedMap.BundleCycles.symmetricGradedMap q)
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant f hf) (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant i hi)
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant q hq) (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant q hq)
    (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective i hi) (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective q hq) h
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation (DoubleHyperplane.BundleCycles.augmentedCoordinateSwap R M)) (DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × (R × M)) _)
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation_kernel (DoubleHyperplane.BundleCycles.augmentedCoordinateSwap R M)) hk (HyperplaneIdealIso.BundleCycles.symmetricLinearChart_cover R (R × (R × M)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneIntersection.BundleCycles
