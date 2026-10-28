import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Kernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification

/-! # Inclusion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles

noncomputable section

/-! The actual projective spectrum of the unaugmented module is the
closed hyperplane complementary to the affine compactification chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def symmetricInfinityInclusion : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩)

instance symmetricInfinityInclusion_isClosedImmersion : IsClosedImmersion (symmetricInfinityInclusion R M) :=
  SymmetricProjective.ClosedImmersion.BundleCycles.symmetricProjectiveMap_isClosedImmersion (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩)

theorem symmetricInfinityInclusion_range :
    Set.range (symmetricInfinityInclusion R M) =
      (↑(Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification R M).opensRange : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M)))ᶜ := by
  change Set.range (Proj.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)) _) = _
  rw [Projective.SurjectiveRange.BundleCycles.projectiveSurjective_range _ _ (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective (LinearMap.snd R R M)
    (fun m => ⟨(0, m), rfl⟩)), Kernel.BundleCycles.symmetricInfinity_kernel, ProjectiveSpectrum.zeroLocus_span,
    Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_opensRange]
  exact ((congrArg Set.compl (ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
    (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M))).trans (compl_compl _)).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles
