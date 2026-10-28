import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FlatConstancy
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ProjectiveCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Projective Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual flat projective family over a noetherian local ring has one Hilbert polynomial on every field-valued fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}

theorem Closed.Families.FlatClosedFamily.localCoefficientField_hilbertPolynomial_iff
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n))
    {K : Type u} [Field K] (φ : CommRingCat.of R ⟶ CommRingCat.of K) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ)
      (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)).homogeneousIdeal.toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial F.homogeneousIdeal.toIdeal P := by
  let : Algebra R K := φ.hom.toAlgebra
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) := F.homogeneousIdeal_flat
  have he := Closed.Families.FlatClosedFamily.homogeneousIdeal_coefficientBaseChange
    (R := CommRingCat.of R) (A := CommRingCat.of K) (n := n) F φ
  rw [he]
  exact Local.FlatConstancy.localFlat_saturatedFieldHilbertPolynomial_iff F.homogeneousIdeal K P

theorem Closed.Families.FlatClosedFamily.localFieldHilbertPolynomial_iff_identity
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n))
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ Spec (.of R)) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback (𝟙 _)).homogeneousIdeal.toIdeal P := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of K := (Spec.fullyFaithful.preimage x).unop
  have he : Spec.map φ = x := Spec.fullyFaithful.map_preimage x
  have hx := F.affineProjectivePullback_coefficient (𝟙 _) φ
  have hc : Spec.map φ ≫ 𝟙 (Spec (.of R)) = x := (Category.comp_id _).trans he
  have hF := (congrArg (fun a => F.affineProjectivePullback a) hc).symm.trans hx
  rw [hF]
  exact (F.affineProjectivePullback (𝟙 _)).localCoefficientField_hilbertPolynomial_iff φ P

theorem Closed.Families.FlatClosedFamily.exists_localFieldHilbertPolynomial
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n)) :
    ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ Spec (.of R)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P := by
  let x := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal
  have hI := (F.localFieldHilbertPolynomial_iff_identity x P).mp hP
  exact ⟨P, fun L _ y => (F.localFieldHilbertPolynomial_iff_identity y P).mpr hI⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
