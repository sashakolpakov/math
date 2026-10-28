import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactFinrank

/-! # Form Function -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormFunction.GradedHilbert

noncomputable section

/-! The Hilbert-function recurrence from an actual regular linear form. -/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem linearForm_hilbertFunction (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hl : l.IsHomogeneous 1)
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, l * f ∈ I.toIdeal → f ∈ I.toIdeal) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d + Hilbert.Polynomial.GradedHilbert.hilbertFunction (FormQuotient.GradedHilbert.linearFormQuotientIdeal I l hl).toIdeal (d + 1) =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (d + 1) := by
  let ℳ := Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I
  let ℙ := Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (FormQuotient.GradedHilbert.linearFormQuotientIdeal I l hl)
  let i := (FormQuotient.GradedHilbert.linearFormScalar I l).restrictScalars K
  let p := (FormQuotient.GradedHilbert.linearFormQuotientMap I l hl).restrictScalars K
  have hi : ∀ e x, x ∈ ReindexedGrading.GradedModules.shiftedGrading ℳ (-1) e → i x ∈ ℳ e := by
    intro e x hx
    change FormQuotient.GradedHilbert.linearFormScalar I l x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I e
    have h := FormQuotient.GradedHilbert.linearFormScalar_homogeneous I l hl (e + -1) x hx
    simpa only [neg_add_cancel_right] using h
  have hp : ∀ e x, x ∈ ℳ e → p x ∈ ℙ e := FormQuotient.GradedHilbert.linearFormQuotientMap_homogeneous I l hl
  let i' := Graded.Exactness.GradedModules.degreeMap (ReindexedGrading.GradedModules.shiftedGrading ℳ (-1)) ℳ i hi ((d + 1 : ℕ) : ℤ)
  let p' := Graded.Exactness.GradedModules.degreeMap ℳ ℙ p hp ((d + 1 : ℕ) : ℤ)
  have hi' : Function.Injective i' := by
    intro x y hxy
    exact Subtype.ext (FormQuotient.GradedHilbert.linearFormScalar_injective I l hreg (congrArg Subtype.val hxy))
  have hp' : Function.Surjective p' := Graded.Exactness.GradedModules.degreeMap_surjective ℳ ℙ p hp
    (FormQuotient.GradedHilbert.linearFormQuotientMap_surjective I l hl) _
  have hex : Function.Exact i' p' := Graded.Exactness.GradedModules.degreeMap_exact (ReindexedGrading.GradedModules.shiftedGrading ℳ (-1)) ℳ ℙ i p hi hp
    (FormQuotient.GradedHilbert.linearFormQuotient_exact I l hl) _
  let E₀ : Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[K] ReindexedGrading.GradedModules.shiftedGrading ℳ (-1) ((d + 1 : ℕ) : ℤ) :=
    (Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d).trans (LinearEquiv.ofEq _ _ (by
      change Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ) = Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (((d + 1 : ℕ) : ℤ) + -1)
      congr 1
      omega))
  let E₁ := Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I (d + 1)
  let E₂ := Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv (FormQuotient.GradedHilbert.linearFormQuotientIdeal I l hl) (d + 1)
  let : Module.Finite K (ℳ ((d + 1 : ℕ) : ℤ)) := Module.Finite.equiv E₁
  have h := ExactFinrank.finrank_add_of_short_exact i' p' hi' hp' hex
  rw [← E₀.finrank_eq, ← E₁.finrank_eq, ← E₂.finrank_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormFunction.GradedHilbert
