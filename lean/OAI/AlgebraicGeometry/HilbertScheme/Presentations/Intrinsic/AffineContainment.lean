import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterFunctor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.SpectrumFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ParameterIsoFactorization

/-! # Affine Containment -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainment.GradedHilbert

noncomputable section

/-! The native affine containment ideal defines a closed parameter
scheme with exact factorization on canonical coefficient-map tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) (R : CommRingCat.{u}) [IsNoetherianRing R]
variable (a : Spec R ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData)

def nativeAffineContainmentScheme : Over S :=
  Over.mk (Quotient.SpectrumFactorization.quotientSpecInclusion R (AffineContainmentIdeal.GradedHilbert.nativeAffineContainmentIdeal n a F K) ≫ a)

def nativeAffineContainmentInclusion : nativeAffineContainmentScheme n R a F K ⟶ Over.mk a :=
  Over.homMk (Quotient.SpectrumFactorization.quotientSpecInclusion R (AffineContainmentIdeal.GradedHilbert.nativeAffineContainmentIdeal n a F K)) rfl

instance nativeAffineContainmentInclusion_isClosedImmersion :
    IsClosedImmersion (nativeAffineContainmentInclusion n R a F K).left :=
  Quotient.SpectrumFactorization.quotientSpecInclusion_isClosedImmersion R _

theorem nativeAffineContainmentInclusion_coefficient_test (A : Type u) [CommRing A] (φ : R →+* A) :
    Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ ∈ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a))) ↔
      ∃ y : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ nativeAffineContainmentScheme n R a F K,
        y ≫ nativeAffineContainmentInclusion n R a F K = Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ :=
  (AffineContainmentIdeal.GradedHilbert.nativeAffineContainmentIdeal_spec n a F K A φ).symm.trans
    ((Quotient.SpectrumFactorization.quotientSpec_lift_iff R (AffineContainmentIdeal.GradedHilbert.nativeAffineContainmentIdeal n a F K) A φ).symm.trans
      (ParameterIsoFactorization.over_exists_lift_iff_left (nativeAffineContainmentInclusion n R a F K) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ)).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainment.GradedHilbert
