import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.DegreeLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.RelativeProjectiveFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFinitePresentation

/-! # Parameter -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Parameter.GradedHilbert

noncomputable section

/-! A constructed locally closed parameter scheme with its actual flat proper
projective family and prescribed residue-fiber Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

def homogeneousResidueIdeal {T : Over S} (x : T ⟶ M) (t : T.left) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading (IsLocalRing.ResidueField (T.left.presheaf.stalk t)) n) :=
  Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
    (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap (T.left.presheaf.stalk t) (IsLocalRing.ResidueField (T.left.presheaf.stalk t)))
      (fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i))) N
    (fun i => ((hg i).map _).map _)

theorem bounded_hilbert_projective_parameter_scheme [IsLocallyNoetherian M.left]
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsImmersion j.left ∧ QuasiCompact j.left ∧
      ∃ e : yoneda.obj Z ≅ (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).toFunctor,
        e.hom ≫ (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).ι = yoneda.map j ∧
        Flat (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) j) ∧
        IsProper (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) j) ∧
        LocallyOfFinitePresentation (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) j) ∧
        ∀ t : Z.left, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (homogeneousResidueIdeal M g N hg j t).toIdeal P := by
  obtain ⟨Z, j, hj, hqc, e, he⟩ := DegreeLocus.GradedHilbert.bounded_hilbert_degree_locus M g N hg q
  have hmem : j ∈ (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).obj (.op Z) :=
    (SubfunctorRepresentations.represented_subfunctor_mem _ j e he Z j).mpr ⟨𝟙 Z, Category.id_comp j⟩
  refine ⟨Z, j, hj, hqc, e, he, ?_, inferInstance, inferInstance, ?_⟩
  · exact Bounded.RelativeProjectiveFlatness.GradedHilbert.bounded_degree_locus_relative_family_flat M g N hg q j
      (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q j hmem)
  · exact fun t => DegreeLocus.GradedHilbert.bounded_hilbert_locus_residue_polynomial M g N hg q P hP j hmem t

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Parameter.GradedHilbert
