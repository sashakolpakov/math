import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.AffineProjectiveFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFamily

/-! # Relative Projective Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.RelativeProjectiveFlatness.GradedHilbert

noncomputable section

/-! The finite represented degree conditions make the actual relative
projective family flat over every test scheme, without noetherian hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem bounded_degree_locus_relative_family_flat (q : ℕ → ℕ) {T : Over S}
    (x : T ⟶ M) (hx : x ∈ (HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    Flat (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x) := by
  apply Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection_flat_of_affine_tests M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) x
  intro U hU a
  apply Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection_flat_of_coefficients
  let : Algebra Γ(M.left, ⊤) Γ(U.left, ⊤) := (a ≫ x).left.appTop.hom.toAlgebra
  rw [Homogeneous.GeneratorsBaseChange.GradedHilbert.homogeneousGeneratorsIdeal_baseChange]
  exact AffineProjectiveFlatness.GradedHilbert.bounded_degree_locus_affine_projective_flat M g N hg q (a ≫ x)
    ((HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).map a.op hx)

/-- An actual parameter scheme and an actual flat universal projective family
for the bounded degree conditions. All representability is constructed. -/
theorem bounded_flat_projective_parameter_scheme (q : ℕ → ℕ) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsImmersion j.left ∧ QuasiCompact j.left ∧
      ∃ e : yoneda.obj Z ≅ (HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).toFunctor,
        e.hom ≫ (HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).ι = yoneda.map j ∧
        Flat (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) j) := by
  obtain ⟨Z, j, hj, hqc, e, he⟩ := HomogeneousFlatLocus.GradedHilbert.bounded_homogeneous_flat_locus M g N hg q
  have hmem : j ∈ (HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op Z) :=
    (SubfunctorRepresentations.represented_subfunctor_mem _ j e he Z j).mpr ⟨𝟙 Z, Category.id_comp j⟩
  exact ⟨Z, j, hj, hqc, e, he, bounded_degree_locus_relative_family_flat M g N hg q j hmem⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.RelativeProjectiveFlatness.GradedHilbert
