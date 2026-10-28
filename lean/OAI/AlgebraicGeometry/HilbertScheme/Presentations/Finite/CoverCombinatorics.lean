import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverReindexing
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

/-! # Cover Combinatorics -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoverCombinatorics.ProjectiveCech

noncomputable section

/-! Casts and coefficient-linear spans of concatenated finite polynomial covers. -/

open _root_.MvPolynomial

universe u v w

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem polynomialCover_cast_exact_iff {n m : ℕ} (h : n = m) (a : Fin m → A)
    (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R A M (a ∘ Fin.cast h) ℳ d q ↔
      Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R A M a ℳ d q := by
  subst m
  rfl

variable {A}

theorem cover_span_le_append_left {n m : ℕ} (a : Fin n → A) (b : Fin m → A) :
    Submodule.span R (Set.range a) ≤ Submodule.span R (Set.range (Fin.append a b)) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castAdd m i, Fin.append_left a b i⟩

theorem cover_span_le_append_right {n m : ℕ} (a : Fin n → A) (b : Fin m → A) :
    Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range (Fin.append a b)) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.natAdd n i, Fin.append_right a b i⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoverCombinatorics.ProjectiveCech
