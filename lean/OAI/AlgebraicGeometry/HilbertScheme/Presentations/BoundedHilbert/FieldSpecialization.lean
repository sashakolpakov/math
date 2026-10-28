import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.DegreeLocus

/-! # Field Specialization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldSpecialization.GradedHilbert

noncomputable section

/-! The bounded Hilbert profile controls every field specialization through
a base stalk, including all extensions of its residue field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u v
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem bounded_hilbert_locus_field_specialization (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T)) (t : T.left)
    {K : Type v} [Field K] (φ : T.left.presheaf.stalk t →+* K) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
      (Finite.SyzygyLifting.GradedHilbert.mapRelationVector φ (fun i => MvPolynomial.map
        ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i))) N
      (fun i => ((hg i).map _).map φ)).toIdeal P := by
  let : Algebra (T.left.presheaf.stalk t) K := φ.toAlgebra
  let gs := fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i)
  have hgs : ∀ i, (gs i).IsHomogeneous N := fun i => (hg i).map _
  have hflat (d : ℕ) : Module.Flat (T.left.presheaf.stalk t)
      (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gs N hgs).toIdeal (d + N)) := by
    have hfree : Module.Free (T.left.presheaf.stalk t)
        (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gs N hgs).toIdeal (d + N)) :=
      Bounded.HomogeneousFlatLocus.GradedHilbert.bounded_degree_locus_all_stalk_quotients_free M g N hg q x
        (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x hx) t d
    let := hfree
    infer_instance
  have hr := (Local.RankTest.GradedHilbert.homogeneous_local_hilbertPolynomial_rank_test
    (K := IsLocalRing.ResidueField (T.left.presheaf.stalk t)) gs N hgs hflat P).mp
      (DegreeLocus.GradedHilbert.bounded_hilbert_locus_residue_polynomial M g N hg q P hP x hx t)
  exact (Local.RankTest.GradedHilbert.homogeneous_local_hilbertPolynomial_rank_test (K := K) gs N hgs hflat P).mpr hr

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldSpecialization.GradedHilbert
