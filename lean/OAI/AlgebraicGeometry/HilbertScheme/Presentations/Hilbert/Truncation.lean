import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Function
import Mathlib.RingTheory.Grassmannian

/-! # Truncation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert

noncomputable section

/-!
A single sufficiently high homogeneous degree determines a saturated
ideal with fixed Hilbert polynomial. This gives the finite-dimensional
Grassmannian coordinates of Hilbert points over every coefficient field.
The relative scheme construction requires, in addition, compatibility of
these quotients with flat families and base change.
-/

open _root_.MvPolynomial

universe u

theorem ideal_le_of_degreeRelations_le {R : Type u} [CommRing R] {n : ℕ}
    (I J : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) (N : ℕ)
    (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) (hB : I = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)))
    (hdeg : ∀ b ∈ B, ∃ d ≤ N, b.IsHomogeneous d) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J)
    (hle : Hilbert.Polynomial.GradedHilbert.degreeRelations I N ≤ Hilbert.Polynomial.GradedHilbert.degreeRelations J N) : I ≤ J := by
  rw [hB]
  apply Ideal.span_le.mpr
  intro b hb
  obtain ⟨d, hd, hbd⟩ := hdeg b hb
  apply hJ b d hbd
  refine ⟨N - d, fun g hg => ?_⟩
  have hgb : g * b ∈ Hilbert.Polynomial.GradedHilbert.grading R n N := by
    change (g * b).IsHomogeneous N
    have h := hg.mul hbd
    simpa only [Nat.sub_add_cancel hd] using h
  have hbI : b ∈ I := by rw [hB]; exact Ideal.subset_span hb
  have hm : (⟨g * b, hgb⟩ : Hilbert.Polynomial.GradedHilbert.grading R n N) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations I N := I.mul_mem_left g hbI
  exact hle hm

theorem exists_uniform_hilbert_data_degree (n : ℕ) (P : Polynomial ℚ) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)),
      Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P →
      (∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
        ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ N, b.IsHomogeneous d) ∧
      ∀ d ≥ N, (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) = P.eval (d : ℚ) := by
  obtain ⟨a, ha⟩ := Uniform.Bound.GradedHilbert.exists_uniform_homogeneous_degree_bound.{u} n P
  obtain ⟨b, hb⟩ := Uniform.Function.GradedHilbert.exists_uniform_hilbertFunction_bound.{u} n P
  refine ⟨max a b, fun K _ I hSat hP => ⟨?_, ?_⟩⟩
  · obtain ⟨B, hB, hhom⟩ := ha K I hSat hP
    refine ⟨B, hB, fun f hf => ?_⟩
    obtain ⟨hf0, d, hd, hfd⟩ := hhom f hf
    exact ⟨hf0, d, hd.trans (le_max_left a b), hfd⟩
  · intro d hd
    exact hb K I hSat hP d ((le_max_right a b).trans hd)

def hilbertParameterDegree (n : ℕ) (P : Polynomial ℚ) : ℕ :=
  (exists_uniform_hilbert_data_degree.{u} n P).choose

theorem hilbertParameterDegree_spec (n : ℕ) (P : Polynomial ℚ)
    (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    (∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
      ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ hilbertParameterDegree.{u} n P, b.IsHomogeneous d) ∧
    ∀ d ≥ hilbertParameterDegree.{u} n P, (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) = P.eval (d : ℚ) :=
  (exists_uniform_hilbert_data_degree.{u} n P).choose_spec K I hSat hP

def SaturatedHilbertIdeals (K : Type u) [Field K] (n : ℕ) (P : Polynomial ℚ) :=
  {I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) // Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal ∧ Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P}

theorem hilbert_degreeRelations_injective (K : Type u) [Field K] (n : ℕ) (P : Polynomial ℚ)
    (N : ℕ) (hN : hilbertParameterDegree.{u} n P ≤ N) :
    Function.Injective (fun I : SaturatedHilbertIdeals K n P => Hilbert.Polynomial.GradedHilbert.degreeRelations I.val.toIdeal N) := by
  intro I J h
  apply Subtype.ext
  apply HomogeneousIdeal.ext
  apply le_antisymm
  · obtain ⟨B, hB, hhom⟩ := (hilbertParameterDegree_spec n P K I.val I.property.1 I.property.2).1
    apply ideal_le_of_degreeRelations_le I.val.toIdeal J.val.toIdeal N B hB _ J.property.1 h.le
    intro f hf
    obtain ⟨_, d, hd, hfd⟩ := hhom f hf
    exact ⟨d, hd.trans hN, hfd⟩
  · obtain ⟨B, hB, hhom⟩ := (hilbertParameterDegree_spec n P K J.val J.property.1 J.property.2).1
    apply ideal_le_of_degreeRelations_le J.val.toIdeal I.val.toIdeal N B hB _ I.property.1 h.ge
    intro f hf
    obtain ⟨_, d, hd, hfd⟩ := hhom f hf
    exact ⟨d, hd.trans hN, hfd⟩

def fieldHilbertGrassmannian (K : Type u) [Field K] (n : ℕ) (P : Polynomial ℚ)
    (I : SaturatedHilbertIdeals K n P) :
    Module.Grassmannian K (Hilbert.Polynomial.GradedHilbert.grading K n (hilbertParameterDegree.{u} n P))
      (P.eval (hilbertParameterDegree.{u} n P : ℚ)).num.toNat where
  toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations I.val.toIdeal (hilbertParameterDegree.{u} n P)
  finite_quotient := Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
  projective_quotient := inferInstance
  rankAtStalk_eq p := by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    have h := (hilbertParameterDegree_spec n P K I.val I.property.1 I.property.2).2
      (hilbertParameterDegree.{u} n P) le_rfl
    rw [← h]
    simp only [Rat.num_natCast, Int.toNat_natCast]
    rfl

/-- The finite-degree Grassmannian coordinates distinguish all Hilbert
points over every field. This is an injection on field-valued points. -/
theorem fieldHilbertGrassmannian_injective (K : Type u) [Field K] (n : ℕ) (P : Polynomial ℚ) :
    Function.Injective (fieldHilbertGrassmannian K n P) := by
  intro I J h
  apply hilbert_degreeRelations_injective K n P (hilbertParameterDegree.{u} n P) le_rfl
  exact congrArg Module.Grassmannian.toSubmodule h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert
