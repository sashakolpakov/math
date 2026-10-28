import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicFiberPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalClassification

/-! # Canonical Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert

noncomputable section

/-! Canonical fiber polynomials use the fixed projective coordinates of
the ambient projective space and are preserved by every test-scheme map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {n : ℕ} {T T' : Over S}

def CanonicalFiberHilbertPolynomial
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ) : Prop :=
  ∀ (K : Type u) [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left),
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (a ≫ T.hom)
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) F)).toIdeal P

theorem CanonicalFiberHilbertPolynomial.over_point
    {F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T} {P : Polynomial ℚ}
    (hP : CanonicalFiberHilbertPolynomial F P) {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ S) (a : Over.mk f ⟶ T) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F)).toIdeal P := by
  generalize hg : a.left = g
  have hf : g ≫ T.hom = f := by rw [← hg]; exact a.w
  have ha : a = Over.homMk g hf := Over.OverMorphism.ext hg
  rw [ha]
  clear ha hg a
  change Spec (.of K) ⟶ T.left at g
  exact Eq.rec (motive := fun (f' : Spec (.of K) ⟶ S) (hf' : g ≫ T.hom = f') =>
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f'
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (Over.homMk g hf' : Over.mk f' ⟶ T) F)).toIdeal P) (hP K g) hf

theorem CanonicalFiberHilbertPolynomial.pullback
    {F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T} {P : Polynomial ℚ}
    (hP : CanonicalFiberHilbertPolynomial F P) (b : T' ⟶ T) :
    CanonicalFiberHilbertPolynomial (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F) P := by
  intro K _ a
  let c : Over.mk (a ≫ T'.hom) ⟶ T' := Over.homMk a rfl
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (a ≫ T'.hom)
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) c
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F))).toIdeal P
  rw [← Hilbert.Functor.pullbackFamily_comp]
  exact hP.over_point (a ≫ T'.hom) (c ≫ b)

theorem CanonicalFiberHilbertPolynomial.affine_residue
    {R : Type u} [CommRing R] {f : Spec (.of R) ⟶ S}
    {F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)} {P : Polynomial ℚ}
    (hP : CanonicalFiberHilbertPolynomial F P) (p : PrimeSpectrum R) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P := by
  have h := hP p.asIdeal.ResidueField (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)) ≫ f)
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R p.asIdeal.ResidueField)) F)).toIdeal P at h
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange] at h
  exact h

theorem canonicalFiberHilbertPolynomial_of_noetherian_affine_residues
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P) :
    CanonicalFiberHilbertPolynomial F P := by
  intro K _ a
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* K, Spec.map (CommRingCat.ofHom φ) = a :=
    ⟨(Spec.preimage a).hom, Spec.map_preimage a⟩
  exact Noetherian.IntrinsicFiberPolynomial.GradedHilbert.noetherian_canonical_field_polynomial f F P hP φ

theorem CanonicalFiberHilbertPolynomial.hasFiberHilbertPolynomial
    {F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T} {P : Polynomial ℚ}
    (hP : CanonicalFiberHilbertPolynomial F P) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P :=
  CanonicalFiberPolynomialCriterion.GradedHilbert.hasFiberHilbertPolynomial_of_canonical_fibers F P hP

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert
