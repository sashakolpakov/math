import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.SyzygyLifting

/-! # Relation Components -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationComponents.GradedHilbert

noncomputable section

/-! Homogeneous components preserve and specialize polynomial relations over arbitrary coefficient rings. -/

open _root_.MvPolynomial DirectSum

universe u v z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable {n : ℕ} {ι : Type z} [Fintype ι]

theorem coordinate_ring_decompose_eq_component (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (d : ℕ) :
    (decompose (Hilbert.Polynomial.GradedHilbert.grading R n) p d).val = homogeneousComponent d p := by
  have he : (inferInstance : Decomposition (Hilbert.Polynomial.GradedHilbert.grading R n)) = MvPolynomial.decomposition := Subsingleton.elim _ _
  exact (congrArg (fun D : Decomposition (Hilbert.Polynomial.GradedHilbert.grading R n) => (D.decompose' p d).val) he).trans
    (MvPolynomial.decomposition.decompose'_apply p d)

theorem homogeneousComponent_mul_homogeneous_right
    (p g : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N d : ℕ) (hg : g.IsHomogeneous N) :
    homogeneousComponent (d + N) (p * g) = homogeneousComponent d p * g := by
  rw [← coordinate_ring_decompose_eq_component, ← coordinate_ring_decompose_eq_component]
  change (decompose (Hilbert.Polynomial.GradedHilbert.grading R n) (p * g) (d + N)).val =
    (decompose (Hilbert.Polynomial.GradedHilbert.grading R n) p d).val * g
  have he := coe_decompose_mul_of_right_mem_of_le (Hilbert.Polynomial.GradedHilbert.grading R n) (a := p) hg (Nat.le_add_left N d)
  have hs : d + N - N = d := by omega
  rw [hs] at he
  exact he

def projectRelationVector (d : ℕ) (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n :=
  fun i => homogeneousComponent d (a i)

omit [Fintype ι] in
theorem projectRelationVector_homogeneous (d : ℕ) (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (i : ι) :
    (projectRelationVector d a i).IsHomogeneous d := homogeneousComponent_isHomogeneous d (a i)

omit [Fintype ι] in
theorem projectRelationVector_of_homogeneous (d : ℕ) (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)
    (ha : ∀ i, (a i).IsHomogeneous d) : projectRelationVector d a = a :=
  funext (fun i => homogeneousComponent_eq_self (ha i))

theorem homogeneousComponent_polynomialRelationMap
    (g a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N d : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    homogeneousComponent (d + N) (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g a) =
      SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g (projectRelationVector d a) := by
  change homogeneousComponent (d + N) (∑ i, a i * g i) = ∑ i, homogeneousComponent d (a i) * g i
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => homogeneousComponent_mul_homogeneous_right (a i) (g i) N d (hg i))

theorem projectRelationVector_relation
    (g a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N d : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (ha : SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g a = 0) : SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g (projectRelationVector d a) = 0 := by
  rw [← homogeneousComponent_polynomialRelationMap g a N d hg, ha, map_zero]

omit [Fintype ι] in
theorem mapRelationVector_project (φ : R →+* S) (d : ℕ) (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    Finite.SyzygyLifting.GradedHilbert.mapRelationVector φ (projectRelationVector d a) = projectRelationVector d (Finite.SyzygyLifting.GradedHilbert.mapRelationVector φ a) := by
  funext i
  apply MvPolynomial.ext
  intro m
  simp only [Finite.SyzygyLifting.GradedHilbert.mapRelationVector, projectRelationVector, coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem homogeneous_relation_lift_of_relation_lift
    (φ : R →+* S) (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N d : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing S n)
    (ha : ∀ i, (a i).IsHomogeneous d)
    (hlift : ∃ b, SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ Finite.SyzygyLifting.GradedHilbert.mapRelationVector φ b = a) :
    ∃ b, (∀ i, (b i).IsHomogeneous d) ∧ SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ Finite.SyzygyLifting.GradedHilbert.mapRelationVector φ b = a := by
  obtain ⟨b, hb, hba⟩ := hlift
  refine ⟨projectRelationVector d b, projectRelationVector_homogeneous d b,
    projectRelationVector_relation g b N d hg hb, ?_⟩
  rw [mapRelationVector_project, hba, projectRelationVector_of_homogeneous d a ha]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationComponents.GradedHilbert
