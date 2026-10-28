import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradingIdeals
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme.BundleCycles

noncomputable section

/-! Actual projective spectra of symmetric algebras, with maps induced
by surjective module maps and isomorphisms induced by changes of frame. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

abbrev symmetricProjectiveScheme : Scheme.{u} := Proj (Symmetric.Grading.BundleCycles.symmetricGrading R M)

def symmetricProjectiveToBase : symmetricProjectiveScheme R M ⟶ Spec (.of R) :=
  Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R M) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom)

variable {R M} {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem symmetricGradedMap_irrelevant (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) := by
  change (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N)).toIdeal ≤
    Ideal.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).toIdeal
  rw [Symmetric.GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal, Symmetric.GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨n, rfl⟩
  obtain ⟨m, rfl⟩ := hf n
  rw [← Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator f m]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, rfl⟩)

def symmetricProjectiveMap (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    symmetricProjectiveScheme R N ⟶ symmetricProjectiveScheme R M :=
  Proj.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (symmetricGradedMap_irrelevant f hf)

theorem symmetricProjectiveMap_congr {f g : M →ₗ[R] N} (h : f = g)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    symmetricProjectiveMap f hf = symmetricProjectiveMap g hg := by
  subst g
  rfl

private theorem gradedProjectiveMap_congr
    {a b : Symmetric.Grading.BundleCycles.symmetricGrading R M →+*ᵍ Symmetric.Grading.BundleCycles.symmetricGrading R N} (h : a = b)
    (ha : HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map a)
    (hb : HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map b) : Proj.map a ha = Proj.map b hb := by
  subst b
  rfl

theorem symmetricProjectiveMap_id :
    symmetricProjectiveMap (LinearMap.id : M →ₗ[R] M) Function.surjective_id = 𝟙 (symmetricProjectiveScheme R M) := by
  exact (gradedProjectiveMap_congr Symmetric.GradedMap.BundleCycles.symmetricGradedMap_id _ (by simp)).trans Proj.map_id

theorem symmetricProjectiveMap_comp (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (g : N →ₗ[R] P) (hg : Function.Surjective g) :
    symmetricProjectiveMap (g.comp f) (hg.comp hf) =
      symmetricProjectiveMap g hg ≫ symmetricProjectiveMap f hf := by
  exact (gradedProjectiveMap_congr (Symmetric.GradedMap.BundleCycles.symmetricGradedMap_comp f g).symm _
    (HomogeneousIdeal.irrelevant_le_map_comp (symmetricGradedMap_irrelevant f hf)
      (symmetricGradedMap_irrelevant g hg))).trans
        (Proj.map_comp (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (Symmetric.GradedMap.BundleCycles.symmetricGradedMap g)
          (symmetricGradedMap_irrelevant f hf) (symmetricGradedMap_irrelevant g hg))

def symmetricProjectiveIso (e : M ≃ₗ[R] N) :
    symmetricProjectiveScheme R M ≅ symmetricProjectiveScheme R N where
  hom := symmetricProjectiveMap e.symm.toLinearMap e.symm.surjective
  inv := symmetricProjectiveMap e.toLinearMap e.surjective
  hom_inv_id := by
    rw [← symmetricProjectiveMap_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext m; exact e.symm_apply_apply m
    exact (symmetricProjectiveMap_congr h _ Function.surjective_id).trans symmetricProjectiveMap_id
  inv_hom_id := by
    rw [← symmetricProjectiveMap_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext n; exact e.apply_symm_apply n
    exact (symmetricProjectiveMap_congr h _ Function.surjective_id).trans symmetricProjectiveMap_id

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme.BundleCycles
