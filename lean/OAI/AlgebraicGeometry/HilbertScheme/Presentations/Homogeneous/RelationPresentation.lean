import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationComponents
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoefficientBaseChange

/-! # Relation Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert

noncomputable section

/-! Finite homogeneous presentations of the degree quotients of an ideal generated in one degree. -/

open _root_.MvPolynomial

universe u z

variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type z} [Fintype ι]

def homogeneousGeneratorsIdeal (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) where
  __ := Ideal.span (Set.range g)
  is_homogeneous' := Ideal.homogeneous_span (Hilbert.Polynomial.GradedHilbert.grading R n) _ (by
    rintro p ⟨i, rfl⟩
    exact ⟨N, hg i⟩)

def homogeneousVectorInclusion (d : ℕ) :
    (ι → Hilbert.Polynomial.GradedHilbert.grading R n d) →ₗ[R] (ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :=
  LinearMap.pi (fun i => (Hilbert.Polynomial.GradedHilbert.grading R n d).subtype.comp (LinearMap.proj i))

theorem polynomialRelationMap_homogeneous
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N d : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (a : ι → Hilbert.Polynomial.GradedHilbert.grading R n d) :
    (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g (homogeneousVectorInclusion d a)).IsHomogeneous (d + N) := by
  apply IsHomogeneous.sum
  intro i _
  exact (a i).property.mul (hg i)

def homogeneousRelationPresentation
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    (ι → Hilbert.Polynomial.GradedHilbert.grading R n d) →ₗ[R] Hilbert.Polynomial.GradedHilbert.grading R n (d + N) :=
  (((SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g).restrictScalars R).comp (homogeneousVectorInclusion d)).codRestrict
    (Hilbert.Polynomial.GradedHilbert.grading R n (d + N)) (polynomialRelationMap_homogeneous g N d hg)

theorem homogeneousRelationPresentation_val
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (d : ℕ) (a : ι → Hilbert.Polynomial.GradedHilbert.grading R n d) :
    (homogeneousRelationPresentation g N hg d a).val = SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g (fun i => (a i).val) := rfl

theorem homogeneousRelationPresentation_range
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    (homogeneousRelationPresentation g N hg d).range =
      Hilbert.Polynomial.GradedHilbert.degreeRelations (homogeneousGeneratorsIdeal g N hg).toIdeal (d + N) := by
  apply le_antisymm
  · rintro f ⟨a, rfl⟩
    change (∑ i, (a i).val * g i) ∈ Ideal.span (Set.range g)
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ (a i).val
      (Ideal.subset_span (Set.mem_range_self i)))
  · intro f hf
    have hfspan : f.val ∈ Submodule.span (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Set.range g) := hf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)).mp hfspan
    have hc' : SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g c = f.val := hc
    have he := congrArg (homogeneousComponent (d + N)) hc'
    rw [RelationComponents.GradedHilbert.homogeneousComponent_polynomialRelationMap g c N d hg,
      homogeneousComponent_eq_self f.property] at he
    refine ⟨fun i => ⟨homogeneousComponent d (c i), homogeneousComponent_isHomogeneous d (c i)⟩, ?_⟩
    exact Subtype.ext he

def homogeneousPresentationCokernelEquiv
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    (Hilbert.Polynomial.GradedHilbert.grading R n (d + N) ⧸ (homogeneousRelationPresentation g N hg d).range) ≃ₗ[R]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (homogeneousGeneratorsIdeal g N hg).toIdeal (d + N) :=
  Submodule.quotEquivOfEq _ _ (homogeneousRelationPresentation_range g N hg d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert
