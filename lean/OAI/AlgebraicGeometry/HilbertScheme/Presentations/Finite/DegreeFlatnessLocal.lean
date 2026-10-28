import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationLifts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness

/-! # Degree Flatness Local -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatnessLocal.GradedHilbert

noncomputable section

/-! A uniform finite-degree flatness test over arbitrary local coefficient rings, proved using bounded syzygies and residue-field relation lifting. -/

open _root_.MvPolynomial

universe u z

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneous_quotients_free_of_finite_flat_degrees
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hflat : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N)))
    (d : ℕ) : Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)) := by
  let K := IsLocalRing.ResidueField R
  let φ := algebraMap R K
  have hφ : Function.Surjective φ := IsLocalRing.residue_surjective
  have hsmall : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      ∀ a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, (∀ i, (a i).IsHomogeneous e) →
        SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (SyzygyLifting.GradedHilbert.mapRelationVector φ g) a = 0 →
        ∃ b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ SyzygyLifting.GradedHilbert.mapRelationVector φ b = a := by
    intro e he a ha hrel
    let := hflat e he
    obtain ⟨b, _, hb, hba⟩ := Homogeneous.PresentationLifts.GradedHilbert.homogeneous_relation_lift_of_flat_quotient hφ g N hg e a ha hrel
    exact ⟨b, hb, hba⟩
  have hall := SyzygyLifting.GradedHilbert.all_relations_lift_of_bounded_homogeneous_lifts φ hφ g N hg hsmall
  have hlift (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (ha : ∀ i, (a i).IsHomogeneous d)
      (hrel : SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (SyzygyLifting.GradedHilbert.mapRelationVector φ g) a = 0) :
      ∃ b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, (∀ i, (b i).IsHomogeneous d) ∧
        SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ SyzygyLifting.GradedHilbert.mapRelationVector φ b = a := by
    apply Homogeneous.RelationComponents.GradedHilbert.homogeneous_relation_lift_of_relation_lift φ g N d hg a ha
    have hm : a ∈ SyzygyLifting.GradedHilbert.liftedPolynomialRelations φ hφ g := by
      rw [hall]
      exact hrel
    exact hm
  let f := Homogeneous.RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d
  have hex := Homogeneous.PresentationLifts.GradedHilbert.homogeneousPresentation_tensor_exact_of_lifts (S := K) g N hg d hlift
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.grading R n (d + N)) := Homogeneous.PresentationBaseChange.GradedHilbert.coordinateDegreeSpace_free (d + N)
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.grading R n (d + N) ⧸ f.range) :=
    LiftedRelationsFlatness.cokernel_free_of_lifted_residue_relations f hex
  exact Module.Free.of_equiv (Homogeneous.RelationPresentation.GradedHilbert.homogeneousPresentationCokernelEquiv g N hg d)

theorem homogeneous_quotients_flat_finite_test
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    (∀ d, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N))) ↔
    (∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N))) := by
  constructor
  · exact fun h e _ => h e
  · intro h d
    let := homogeneous_quotients_free_of_finite_flat_degrees g N hg h d
    infer_instance

theorem projectiveQuotient_flat_of_finite_degree_test_local
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hflat : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N))) :
    AlgebraicGeometry.Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg))) := by
  apply Projective.Flatness.GradedHilbert.projectiveQuotient_flat_of_eventually_flat (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) N
  intro d hd
  have he : d - N + N = d := Nat.sub_add_cancel hd
  rw [← he]
  exact (homogeneous_quotients_flat_finite_test g N hg).mpr hflat (d - N)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatnessLocal.GradedHilbert
