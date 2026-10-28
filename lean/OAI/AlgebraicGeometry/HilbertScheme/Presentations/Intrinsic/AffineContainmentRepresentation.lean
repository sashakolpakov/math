import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentSpectrumTests
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterRepresentation

/-! # Affine Containment Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentRepresentation.GradedHilbert

noncomputable section

/-! For a native flat projective family over an affine noetherian
parameter scheme, actual ideal containment is represented by the
constructed closed subscheme on every test scheme, naturally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) (R : CommRingCat.{u}) [IsNoetherianRing R]
variable (a : Spec R ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData)

theorem nativeAffineContainmentInclusion_all_tests (T : Over S) (x : T ⟶ Over.mk a) :
    K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x) ≤
      (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x F).val ↔
        ∃! y : T ⟶ AffineContainment.GradedHilbert.nativeAffineContainmentScheme n R a F K,
          y ≫ AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n R a F K = x :=
  Ideal.ContainmentParameterRepresentation.Hilbert.idealContainmentParameter_lifts (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val
    (AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n R a F K)
    (AffineContainmentSpectrumTests.GradedHilbert.nativeAffineContainmentInclusion_spectrum_test n R a F K) T x

theorem nativeAffineContainmentRepresentation :
    ∃ e : yoneda.obj (AffineContainment.GradedHilbert.nativeAffineContainmentScheme n R a F K) ≅
        (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).toFunctor,
      e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).ι =
        yoneda.map (AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n R a F K) :=
  Ideal.ContainmentParameterRepresentation.Hilbert.idealContainmentParameter_representation (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val
    (AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n R a F K)
    (AffineContainmentSpectrumTests.GradedHilbert.nativeAffineContainmentInclusion_spectrum_test n R a F K)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentRepresentation.GradedHilbert
