import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PrimeDescent

/-! # Generated Saturation Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedSaturationNeighborhood.GradedHilbert

noncomputable section

/-! Equality of the projective subschemes cut out by two finite homogeneous
lists is open around a coefficient prime where they agree. -/

open _root_.MvPolynomial

universe u v w
variable {A : Type u} [CommRing A] {n : ℕ}

theorem mapped_generator_mem_projectiveSaturation
    (T : Type v) [CommRing T] [Algebra A T]
    {κ : Type w} (g : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (i : κ) :
    MvPolynomial.map (algebraMap A T) (g i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg))).toIdeal :=
  Projective.Saturation.GradedHilbert.le_projectiveSaturation _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i)))

theorem generated_projectiveSaturation_equality_neighborhood
    (p : Ideal A) [p.IsPrime]
    {ι : Type v} [Fintype ι] {κ : Type w} [Fintype κ]
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (h : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) (M : ℕ) (hh : ∀ i, (h i).IsHomogeneous M)
    (he : Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p)
        (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p)
        (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h M hh))) :
    ∃ s : A, s ∉ p ∧
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.Away s)
        (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.Away s)
        (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h M hh)) := by
  let I := Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg
  let J := Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h M hh
  let target : ι ⊕ κ → HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n) := Sum.elim (fun _ => J) (fun _ => I)
  let polys : ι ⊕ κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n := Sum.elim g h
  let degree : ι ⊕ κ → ℕ := Sum.elim (fun _ => N) (fun _ => M)
  have hdegree : ∀ i, (polys i).IsHomogeneous (degree i) := by
    intro i
    cases i with
    | inl i => exact hg i
    | inr i => exact hh i
  have hmem (i : ι ⊕ κ) : MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (polys i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p) (target i))).toIdeal := by
    cases i with
    | inl i =>
      exact he ▸ mapped_generator_mem_projectiveSaturation (Localization.AtPrime p) g N hg i
    | inr i =>
      exact he.symm ▸ mapped_generator_mem_projectiveSaturation (Localization.AtPrime p) h M hh i
  obtain ⟨s, hs, hsm⟩ := Saturation.PrimeDescent.GradedHilbert.finite_saturation_membership_prime_descent p target polys degree hdegree hmem
  refine ⟨s, hs, le_antisymm ?_ ?_⟩
  · exact Saturation.PrimeDescent.GradedHilbert.generatedIdeal_le_saturation_of_mapped_generators (Localization.Away s) g N hg J
      (fun i => hsm (.inl i))
  · exact Saturation.PrimeDescent.GradedHilbert.generatedIdeal_le_saturation_of_mapped_generators (Localization.Away s) h M hh I
      (fun i => hsm (.inr i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedSaturationNeighborhood.GradedHilbert
