import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChartKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealAffineCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecPrincipalImageIdeal

/-! # Bundle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle.Cycles

noncomputable section

/-! The infinity hyperplane of the actual augmented symmetric Proj
has a genuine invertible ideal sheaf. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricInfinity_regularPrincipalImageIdeals :
    Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (Inclusion.BundleCycles.symmetricInfinityInclusion R M) := by
  let f := Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)
  let hf := SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩)
  apply Cartier.IdealAffineCover.BundleCycles.regularPrincipalImageIdeals_of_affineCover (Inclusion.BundleCycles.symmetricInfinityInclusion R M)
    (Symmetric.DegreeOneCover.BundleCycles.symmetricDegreeOneCover R (R × M)).openCover (fun v => by
      change IsAffine (Spec (.of (Away (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
        (SymmetricAlgebra.ι R (R × M) v))))
      infer_instance)
    (fun v => Spec (.of (Away (Symmetric.Grading.BundleCycles.symmetricGrading R M) (f (SymmetricAlgebra.ι R (R × M) v)))))
    (fun v => Proj.awayι (Symmetric.Grading.BundleCycles.symmetricGrading R M) (f (SymmetricAlgebra.ι R (R × M) v))
      (f.map_mem (Symmetric.DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v)) (by decide : 0 < 1))
    (fun v => Spec.map (CommRingCat.ofHom (Away.map f (SymmetricAlgebra.ι R (R × M) v))))
    (fun v => Projective.MapChartPullback.BundleCycles.projectiveMap_chart_isPullback f hf (Symmetric.DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v) (by decide : 0 < 1))
    (fun v => (Scheme.ΓSpecIso (.of (Away (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricAlgebra.ι R (R × M) v)))).inv (Symmetric.HyperplaneCharts.BundleCycles.symmetricHyperplaneCoordinate R M v))
  · intro v
    exact SpecPrincipalImageIdeal.BundleCycles.spec_regular_globalSection _ (Symmetric.HyperplaneCharts.BundleCycles.symmetricHyperplaneCoordinate_isRegular R M v)
  · intro v
    exact SpecPrincipalImageIdeal.BundleCycles.specMap_principal_kernel _ _ (ChartKernel.BundleCycles.symmetricInfinity_chart_kernel R M v)

def symmetricInfinityIdealLineBundle : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M)) :=
  Cartier.IdealBundle.Cycles.cartierIdealLineBundle (Inclusion.BundleCycles.symmetricInfinityInclusion R M) (symmetricInfinity_regularPrincipalImageIdeals R M)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle.Cycles
