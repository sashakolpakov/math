import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ModuleCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient

/-! # Zero Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroCech.GradedHilbert

noncomputable section

/-! Uniform Čech exactness for every saturated homogeneous coordinate quotient of projective zero-space. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ModuleCech.ProjectiveCech

universe u

theorem coordinateCechExactAt_of_bot {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : I.toIdeal = ⊥) (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  let f := (Ideal.Quotient.mkₐ (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) I.toIdeal).toLinearMap
  have hf (a : ℤ) (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R a) :
      f p ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I a := ⟨p, hp, rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h : x - y ∈ I.toIdeal := Ideal.Quotient.eq.mp hxy
      rw [hI, Submodule.mem_bot] at h
      exact sub_eq_zero.mp h
    · exact Ideal.Quotient.mk_surjective
  exact (Cech.ModuleIsomorphism.ProjectiveCech.moduleCechExactAt_iff_of_module_bijective R (WeightedFreeModules.GradedModules.polynomialIntegerGrading R)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) f hf hbij d q).mp (Polynomial.ModuleCech.ProjectiveCech.polynomialModuleCech_exactAt R d hd q)

theorem coordinateCechExactAt_of_top {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : I.toIdeal = ⊤) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  have hsub : Subsingleton (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) := by
    rw [hI]
    infer_instance
  let := hsub
  exact Polynomial.ModuleCech.ProjectiveCech.moduleCechExactAt_of_subsingleton R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q

theorem projectiveZero_moduleCechExactAt {K : Type u} [Field K]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K 0)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin 1) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K 0 ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  obtain hI | hI := ZeroIdeals.GradedHilbert.projectiveZero_saturated_ideal_eq_bot_or_top I hSat
  · exact coordinateCechExactAt_of_bot I hI d hd q
  · exact coordinateCechExactAt_of_top I hI d q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroCech.GradedHilbert
