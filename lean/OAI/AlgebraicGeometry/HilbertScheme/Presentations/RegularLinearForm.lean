import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularInitialIdeal
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.Submodule.Union

/-! # Regular Linear Form -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularLinearForm.GradedHilbert

noncomputable section

/-!
Saturation excludes associated primes containing all linear forms. Over
an infinite field, finite subspace avoidance therefore produces a regular
linear form on the homogeneous coordinate quotient.
-/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem saturated_mem_of_linear_multiples (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (hf : ∀ g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, g.IsHomogeneous 1 → g * f ∈ I.toIdeal) :
    f ∈ I.toIdeal := by
  apply (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading K n) I.isHomogeneous).mpr
  intro d
  apply hSat ((DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading K n) f d).val) d
    (DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading K n) f d).property
  refine ⟨1, fun g hg => ?_⟩
  have h := (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading K n) I.isHomogeneous).mp (hf g hg) (1 + d)
  rw [DirectSum.coe_decompose_mul_add_of_left_mem (Hilbert.Polynomial.GradedHilbert.grading K n) hg] at h
  exact h

theorem associatedPrime_linearPart_ne_top (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (P : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (hP : P ∈ associatedPrimes (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)) :
    (P.restrictScalars K).comap (Hilbert.Polynomial.GradedHilbert.grading K n 1).subtype ≠ ⊤ := by
  intro htop
  obtain ⟨hprime, x, hPx⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hf : f ∈ I.toIdeal := by
    apply saturated_mem_of_linear_multiples I hSat f
    intro g hg
    have hPg : g ∈ P := by
      have hmem : (⟨g, hg⟩ : Hilbert.Polynomial.GradedHilbert.grading K n 1) ∈
          (P.restrictScalars K).comap (Hilbert.Polynomial.GradedHilbert.grading K n 1).subtype := by
        rw [htop]
        exact Submodule.mem_top
      exact hmem
    rw [hPx] at hPg
    have hz := Submodule.mem_colon_singleton.mp hPg
    change g • Ideal.Quotient.mk I.toIdeal f = 0 at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [hzero, Submodule.colon_singleton_zero] at hPx
  exact hprime.ne_top hPx

theorem exists_regular_linear_form [Infinite K]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) :
    ∃ l : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, l.IsHomogeneous 1 ∧ l ≠ 0 ∧
      ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, l * f ∈ I.toIdeal → f ∈ I.toIdeal := by
  classical
  by_cases htop : I.toIdeal = ⊤
  · refine ⟨X 0, isHomogeneous_X K 0, X_ne_zero 0, fun f _ => ?_⟩
    rw [htop]
    exact Submodule.mem_top
  let Ass := associatedPrimes (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
  let : Fintype Ass := (associatedPrimes.finite (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)).fintype
  let p (P : Ass) : Submodule K (Hilbert.Polynomial.GradedHilbert.grading K n 1) :=
    (P.val.restrictScalars K).comap (Hilbert.Polynomial.GradedHilbert.grading K n 1).subtype
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p
    (fun P => associatedPrime_linearPart_ne_top I hSat P.val P.property)
  have hlreg : IsSMulRegular (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) l.val := by
    by_contra hreg
    have hmem : l.val ∈ {r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n |
        IsSMulRegular (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) r}ᶜ := hreg
    rw [← biUnion_associatedPrimes_eq_compl_regular] at hmem
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨hPass, hPl⟩ := Set.mem_iUnion.mp hP
    exact hl ⟨P, hPass⟩ hPl
  have hcancel (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : l.val * f ∈ I.toIdeal) : f ∈ I.toIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply isSMulRegular_iff_right_eq_zero_of_smul.mp hlreg
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
  refine ⟨l.val, l.property, ?_, hcancel⟩
  intro hlzero
  apply htop
  apply eq_top_iff.mpr
  intro f _
  apply hcancel f
  rw [hlzero, zero_mul]
  exact I.toIdeal.zero_mem

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularLinearForm.GradedHilbert
