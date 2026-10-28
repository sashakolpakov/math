import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainment

/-! # Affine Containment Spectrum Tests -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentSpectrumTests.GradedHilbert

noncomputable section

/-! The native affine containment scheme has its exact factorization
criterion on every spectrum-valued test with its given map to the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) (R : CommRingCat.{u}) [IsNoetherianRing R]
variable (a : Spec R ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData)

theorem nativeAffineContainmentInclusion_spectrum_test (A : Type u) [CommRing A]
    (b : Spec (CommRingCat.of A) ⟶ S) (x : Over.mk b ⟶ Over.mk a) :
    x ∈ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).obj
      (.op (Over.mk b)) ↔ ∃ y : Over.mk b ⟶ AffineContainment.GradedHilbert.nativeAffineContainmentScheme n R a F K,
        y ≫ AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n R a F K = x := by
  let φ : R →+* A := (Spec.preimage x.left).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = x.left := Spec.map_preimage x.left
  let V : Over S := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a)
  let e : V ≅ Over.mk b := Over.isoMk (Iso.refl (Spec (CommRingCat.of A))) (by
    change (𝟙 _) ≫ b = Spec.map (CommRingCat.ofHom φ) ≫ a
    rw [Category.id_comp, hφ]
    exact x.w.symm)
  have hx : e.hom ≫ x = Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ := by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ x.left = Spec.map (CommRingCat.ofHom φ)
    exact (Category.id_comp _).trans hφ.symm
  let L := Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val
  have h := AffineContainment.GradedHilbert.nativeAffineContainmentInclusion_coefficient_test n R a F K A φ
  rw [← hx] at h
  exact (ParameterIsoFactorization.subfunctor_mem_comp_iso_iff L e x).symm.trans
    (h.trans (ParameterIsoFactorization.exists_lift_comp_iso_iff e (AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n R a F K) x))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentSpectrumTests.GradedHilbert
