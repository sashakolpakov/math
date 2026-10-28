import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianProjectiveComparisons
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AutomorphismPolynomial

/-! # Exact Canonical Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactCanonicalFiberPolynomial.GradedHilbert

noncomputable section

/-! The exact statement predicate, allowing any Cartesian projective
coordinate comparison, is equivalent to the canonical fiber polynomial. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {n : ℕ} {T : Over S}

theorem canonicalFiberHilbertPolynomial_of_hasFiberHilbertPolynomial
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P) :
    CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P := by
  intro K _ a
  let b : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F
  have hp := hP K a
  dsimp only [Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation] at hp
  obtain ⟨q, f, hq, hf, hinc, hproj, hpoly⟩ := hp
  let q₀ := Projective.Point.GradedHilbert.projectiveSchemePointMap n (a ≫ T.hom)
  let f₀ := Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding n (a ≫ T.hom) G
  have hq₀ := Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n (a ≫ T.hom)
  let e := CartesianProjectiveComparisons.cartesianProjectiveComparisonIso (a ≫ T.hom) q₀ q hq₀ hq
  have hi : f₀ ≫ q₀ = f ≫ q := by
    erw [Category.comp_id] at hinc
    exact (Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_ambient n (a ≫ T.hom) G).trans hinc.symm
  have hb : f₀ ≫ Has.Core.projectiveSpaceMap K n = f ≫ Has.Core.projectiveSpaceMap K n :=
    (Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_projection n (a ≫ T.hom) G).trans hproj.symm
  have he : f₀ ≫ e.hom = f :=
    CartesianProjectiveComparisons.cartesianProjectiveComparisonIso_embedding (a ≫ T.hom) q₀ q hq₀ hq f₀ f hi hb
  have hpoly₀ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (f₀ ≫ e.hom).ker).toIdeal P := by
    rw [he]
    exact hpoly
  have h := (Projective.AutomorphismPolynomial.projectiveAutomorphism_hilbertPolynomial_iff K e
    (CartesianProjectiveComparisons.cartesianProjectiveComparisonIso_native_base (a ≫ T.hom) q₀ q hq₀ hq) f₀ P).mp hpoly₀
  rwa [Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_coordinates] at h

theorem hasFiberHilbertPolynomial_iff_canonical
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P ↔
      CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P :=
  ⟨canonicalFiberHilbertPolynomial_of_hasFiberHilbertPolynomial F P,
    CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial.hasFiberHilbertPolynomial⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactCanonicalFiberPolynomial.GradedHilbert
