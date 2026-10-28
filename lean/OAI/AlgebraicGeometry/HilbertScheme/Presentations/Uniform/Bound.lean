import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ScalarExtension
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Bound.GradedHilbert

noncomputable section

/-!
Uniform bounded generation over arbitrary coefficient fields. Bounded
generation descends along a field extension by applying linear functionals
to coefficients, and the rational-function extension supplies an infinite
coefficient field without changing saturation or the Hilbert polynomial.
-/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {n : ℕ}

def boundedHomogeneousForms (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (N : ℕ) : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  {f | f ∈ I ∧ f ≠ 0 ∧ ∃ d ≤ N, f.IsHomogeneous d}

theorem bounded_generation_descends (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (N : ℕ)
    (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n))
    (hB : CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n)))
    (hhom : ∀ b ∈ B, ∃ d ≤ N, b.IsHomogeneous d) :
    ∃ F : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I = Ideal.span (F : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
      ∀ f ∈ F, f ≠ 0 ∧ ∃ d ≤ N, f.IsHomogeneous d := by
  classical
  let S := boundedHomogeneousForms I N
  let J := Ideal.span S
  have hJI : J ≤ I := Ideal.span_le.mpr fun _ hf => hf.1
  have hExt : CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I ≤ CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) J := by
    rw [hB]
    apply Ideal.span_le.mpr
    intro b hb
    apply (ScalarExtension.GradedHilbert.mem_scalarExtendedIdeal_iff J b).mpr
    intro φ
    by_cases hzero : CoefficientMaps.GradedHilbert.coefficientApply φ b = 0
    · rw [hzero]
      exact J.zero_mem
    · obtain ⟨d, hd, hbd⟩ := hhom b hb
      apply Ideal.subset_span
      refine ⟨?_, hzero, d, hd, CoefficientMaps.GradedHilbert.coefficientApply_homogeneous φ hbd⟩
      apply CoefficientMaps.GradedHilbert.coefficientApply_mem_of_mem_scalarExtendedIdeal I φ
      rw [hB]
      exact Ideal.subset_span hb
  have hIJ : I ≤ J := by
    intro f hf
    apply (ScalarExtension.GradedHilbert.map_mem_scalarExtendedIdeal_iff (L := L) J f).mp
    apply hExt
    exact (ScalarExtension.GradedHilbert.map_mem_scalarExtendedIdeal_iff (L := L) I f).mpr hf
  have hIeq : I = J := le_antisymm hIJ hJI
  have hfg : (Submodule.span (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) S).FG := J.fg_of_isNoetherianRing
  obtain ⟨F, hFS, hF⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) S).mp hfg
  refine ⟨F, hIeq.trans hF, fun f hf => ?_⟩
  exact (hFS hf).2

/-- The uniform boundedness theorem for saturated homogeneous coordinate
ideals over all fields. The bound depends only on the number of variables
and the specified Hilbert polynomial. -/
theorem exists_uniform_homogeneous_degree_bound (n : ℕ) (P : Polynomial ℚ) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)),
      Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P →
      ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
        ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ N, b.IsHomogeneous d := by
  obtain ⟨N, hN⟩ := InfiniteFieldBound.GradedHilbert.exists_uniform_homogeneous_degree_bound_infinite.{u} n P
  refine ⟨N, fun K _ I hSat hP => ?_⟩
  let : Infinite (RatFunc K) := Infinite.of_injective _ (RatFunc.algebraMap_injective K)
  let J := ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := RatFunc K) I
  have hSatJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal := ScalarExtension.GradedHilbert.scalarExtendedIdeal_isSaturated I.toIdeal hSat
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P :=
    (Hilbert.ScalarExtension.GradedHilbert.hasHilbertPolynomial_scalarExtended_iff I P).mpr hP
  obtain ⟨B, hB, hhom⟩ := hN (RatFunc K) J hSatJ hPJ
  exact bounded_generation_descends I.toIdeal N B hB (fun b hb => (hhom b hb).2)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Bound.GradedHilbert
