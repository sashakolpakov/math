import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading

/-! # Base -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base.BundleCycles

noncomputable section

section

/-! Projectivized coefficient changes commute with the actual maps to
the spectra of the coefficient rings. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

theorem symmetricScalarDegreeZero_square :
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f g).gradedZeroRingHom.comp (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom =
      (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero S N).toRingHom.comp f := by
  ext r
  exact Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap f g r

theorem symmetricScalarProjectiveMap_over (hgen : Submodule.span S (Set.range g) = ⊤) :
    Symmetric.ScalarGrading.BundleCycles.symmetricScalarProjectiveMap f g hgen ≫ Scheme.BundleCycles.symmetricProjectiveToBase R M =
      Scheme.BundleCycles.symmetricProjectiveToBase S N ≫ Spec.map (CommRingCat.ofHom f) := by
  change Proj.map (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f g) _ ≫
      (Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R M) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom)) =
    (Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading S N) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero S N).toRingHom)) ≫ _
  rw [← Category.assoc, Projective.MapBase.BundleCycles.projectiveMap_toSpecZero, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun h : R →+* Symmetric.Grading.BundleCycles.symmetricGrading S N 0 => Spec.map (CommRingCat.ofHom h))
    (symmetricScalarDegreeZero_square f g)

end

/-! Projectivized surjective module maps preserve the actual base projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)

theorem symmetricProjectiveMap_over :
    Scheme.BundleCycles.symmetricProjectiveMap g hg ≫ Scheme.BundleCycles.symmetricProjectiveToBase R M = Scheme.BundleCycles.symmetricProjectiveToBase R N := by
  have hz : (Symmetric.GradedMap.BundleCycles.symmetricGradedMap g).gradedZeroRingHom.comp (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom =
      (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R N).toRingHom := by
    ext r
    exact (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp g)).commutes r
  change Proj.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap g) _ ≫
    (Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R M) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom)) =
    Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R N).toRingHom)
  rw [← Category.assoc, Projective.MapBase.BundleCycles.projectiveMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  exact congrArg (fun h : R →+* Symmetric.Grading.BundleCycles.symmetricGrading R N 0 =>
    Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≫ Spec.map (CommRingCat.ofHom h)) hz

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base.BundleCycles
