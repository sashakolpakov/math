import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.Changes

/-! # Infinite Field Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldBound.GradedHilbert

noncomputable section

/-!
Uniform bounded generation of saturated homogeneous coordinate ideals
over infinite fields. Coordinate changes preserve graded quotient
dimensions and reduce the problem to a regular coordinate variable.
-/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

def degreeChange (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.grading K n d ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n d where
  toFun f := ⟨Linear.Changes.GradedHilbert.extendLinearEquiv e f.val, Linear.Changes.GradedHilbert.extendLinearEquiv_homogeneous e f.property⟩
  invFun f := ⟨(Linear.Changes.GradedHilbert.extendLinearEquiv e).symm f.val, Linear.Changes.GradedHilbert.extendLinearEquiv_homogeneous e.symm f.property⟩
  left_inv f := Subtype.ext ((Linear.Changes.GradedHilbert.extendLinearEquiv e).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((Linear.Changes.GradedHilbert.extendLinearEquiv e).apply_symm_apply f.val)
  map_add' f g := Subtype.ext (map_add (Linear.Changes.GradedHilbert.extendLinearEquiv e) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (Linear.Changes.GradedHilbert.extendLinearEquiv e).toLinearMap r f.val)

theorem comap_linearChange_isHomogeneous (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) :
    (I.toIdeal.comap (Linear.Changes.GradedHilbert.extendLinearEquiv e).toRingHom).IsHomogeneous (Hilbert.Polynomial.GradedHilbert.grading K n) := by
  obtain ⟨N, B, hB, hhom⟩ := GroebnerGenerators.GradedHilbert.exists_finite_homogeneous_generators MonomialOrder.lex I
  have heq : I.toIdeal.comap (Linear.Changes.GradedHilbert.extendLinearEquiv e).toRingHom =
      I.toIdeal.map (Linear.Changes.GradedHilbert.extendLinearEquiv e).symm.toRingHom :=
    (Ideal.map_symm (I := I.toIdeal) (Linear.Changes.GradedHilbert.extendLinearEquiv e).toRingEquiv).symm
  rw [heq, hB, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨_, d, _, hd⟩ := hhom b hb
  exact ⟨d, Linear.Changes.GradedHilbert.extendLinearEquiv_homogeneous e.symm hd⟩

def changedIdeal (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) :=
  ⟨I.toIdeal.comap (Linear.Changes.GradedHilbert.extendLinearEquiv e).toRingHom, comap_linearChange_isHomogeneous e I⟩

theorem degreeRelations_map_change (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    (Hilbert.Polynomial.GradedHilbert.degreeRelations (changedIdeal e I).toIdeal d).map (degreeChange e d).toLinearMap =
      Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  apply Submodule.ext
  intro y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(degreeChange e d).symm y, ?_, (degreeChange e d).apply_symm_apply y⟩
    change Linear.Changes.GradedHilbert.extendLinearEquiv e ((Linear.Changes.GradedHilbert.extendLinearEquiv e).symm y.val) ∈ I.toIdeal
    rw [(Linear.Changes.GradedHilbert.extendLinearEquiv e).apply_symm_apply]
    exact hy

def degreeQuotientChange (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.DegreeQuotient (changedIdeal e I).toIdeal d ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d :=
  Submodule.Quotient.equiv _ _ (degreeChange e d) (degreeRelations_map_change e I d)

theorem hilbertFunction_changedIdeal (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (changedIdeal e I).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d :=
  (degreeQuotientChange e I d).finrank_eq

theorem hasHilbertPolynomial_changedIdeal_iff (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (changedIdeal e I).toIdeal P ↔ Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  simp only [Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, hilbertFunction_changedIdeal]

/-- Over every infinite coefficient field, saturated homogeneous ideals
with the fixed Hilbert polynomial have homogeneous generators in uniformly
bounded degrees. The bound depends only on n and P. -/
theorem exists_uniform_homogeneous_degree_bound_infinite (n : ℕ) (P : Polynomial ℚ) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] [Infinite K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)),
      Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P →
      ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
        ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ N, b.IsHomogeneous d := by
  classical
  obtain ⟨N, hN⟩ := RegularInitialIdeal.GradedHilbert.exists_uniform_homogeneous_degree_bound_of_variableRegular.{u} n P
  refine ⟨N, fun K _ _ I hSat hP => ?_⟩
  obtain ⟨l, hl, hl0, hreg⟩ := RegularLinearForm.GradedHilbert.exists_regular_linear_form I hSat
  obtain ⟨e, he⟩ := Linear.Changes.GradedHilbert.exists_coordinate_change l hl hl0
  let E := Linear.Changes.GradedHilbert.extendLinearEquiv e
  have hJreg : RegularInitialIdeal.GradedHilbert.VariableRegular (changedIdeal e I).toIdeal 0 := by
    intro f hf
    apply hreg
    change E (X 0 * f) ∈ I.toIdeal at hf
    rw [map_mul, he] at hf
    exact hf
  obtain ⟨B, hB, hhom⟩ := hN K (changedIdeal e I) 0 hJreg
    ((hasHilbertPolynomial_changedIdeal_iff e I P).mpr hP)
  refine ⟨B.image E, ?_, ?_⟩
  · have hmap : ((changedIdeal e I).toIdeal).map E.toRingHom = I.toIdeal :=
      Ideal.map_comap_of_surjective _ E.surjective _
    rw [hB, Ideal.map_span] at hmap
    rw [← hmap, Finset.coe_image]
    rfl
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨ha0, d, hd, had⟩ := hhom a ha
    refine ⟨fun hz => ha0 (E.injective (hz.trans (map_zero E).symm)), d, hd, ?_⟩
    exact Linear.Changes.GradedHilbert.extendLinearEquiv_homogeneous e had

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldBound.GradedHilbert
