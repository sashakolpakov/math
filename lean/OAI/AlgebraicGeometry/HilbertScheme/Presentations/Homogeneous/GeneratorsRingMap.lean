import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange

/-! # Generators Ring Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsRingMap.GradedHilbert

noncomputable section

/-! Ring-homomorphism and finite reindexing formulas for actual generated
homogeneous ideals. -/

universe u v w z
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A]
variable {n : ℕ} {ι : Type w} {κ : Type z}

theorem homogeneousGeneratorsIdeal_map_ringHom (φ : R →+* A)
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) =
      RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (fun i => MvPolynomial.map φ (g i)) N (fun i => (hg i).map φ) := by
  apply HomogeneousIdeal.ext
  change Ideal.map (MvPolynomial.map φ) (Ideal.span (Set.range g)) =
    Ideal.span (Set.range (fun i => MvPolynomial.map φ (g i)))
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem homogeneousGeneratorsIdeal_reindex (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) (e : κ → ι) (he : Function.Surjective e) :
    RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (g ∘ e) N (fun j => hg (e j)) = RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg := by
  apply HomogeneousIdeal.ext
  change Ideal.span (Set.range (g ∘ e)) = Ideal.span (Set.range g)
  rw [Set.range_comp, he.range_eq, Set.image_univ]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsRingMap.GradedHilbert
