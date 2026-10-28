import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.CechVanishing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cech Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechExactness

noncomputable section

/-! Graded coordinate Čech exactness implies exactness of the actual module complex. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateCechComplex_exactAt_of_gradedExact (d : ℤ) (q : ℕ)
    (h : HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)) :
    (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d).ExactAt (q + 1) := by
  let C := HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d
  apply (C.exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) x.val = 0 :=
    congrArg Subtype.val ((ConcreteCategory.congr_hom
      (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1))
        x).symm.trans hx)
  obtain ⟨g, hg, hcard, hgd⟩ := h x.val x.property.1 x.property.2 hx'
  have hcard' : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) q g := by
    simpa only [Nat.add_sub_cancel] using hcard
  let y : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := ⟨g, hg, hcard'⟩
  have hy : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q y = x := Subtype.ext hgd
  exact ⟨y, (ConcreteCategory.congr_hom
    (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q)
      y).trans hy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechExactness
