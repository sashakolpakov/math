import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.FamilyComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveCriterion

/-! # Local Coefficient Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every flat projective closed family over a Noetherian local coefficient ring has a single Hilbert polynomial after all field coefficient extensions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Closed.Families.FlatClosedFamily.exists_localCoefficientFieldHilbertPolynomial
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) :
    ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] (φ : CommRingCat.of R ⟶ CommRingCat.of K),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Closed.Families.FlatClosedFamily.homogeneousIdeal (R := K) (n := n) (F.coefficientPullback φ)).toIdeal P := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of (IsLocalRing.ResidueField R) :=
    CommRingCat.ofHom (IsLocalRing.residue R)
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (Closed.Families.FlatClosedFamily.homogeneousIdeal (R := IsLocalRing.ResidueField R) (n := n) (F.coefficientPullback φ))
  have hF := (F.localCoefficientField_hilbertPolynomial_iff φ P).mp hP
  exact ⟨P, fun K _ ψ => (F.localCoefficientField_hilbertPolynomial_iff ψ P).mpr hF⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
