import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularQuotientCech
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Form Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormQuotient.GradedHilbert

noncomputable section

/-! The actual graded exact sequence obtained by quotienting a homogeneous coordinate ring by a linear form. -/

open _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def linearFormIdeal (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) where
  __ := Ideal.span {l}
  is_homogeneous' := Ideal.homogeneous_span (Hilbert.Polynomial.GradedHilbert.grading R n) {l} (by
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨1, hl⟩)

def linearFormQuotientIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  I ⊔ linearFormIdeal l hl

def linearFormQuotientMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) →ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing R n]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (linearFormQuotientIdeal I l hl).toIdeal :=
  (Ideal.Quotient.factorₐ (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (show I.toIdeal ≤
    (linearFormQuotientIdeal I l hl).toIdeal from le_sup_left)).toLinearMap

theorem linearFormQuotientMap_surjective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) :
    Function.Surjective (linearFormQuotientMap I l hl) :=
  Ideal.Quotient.factor_surjective (show I.toIdeal ≤ (linearFormQuotientIdeal I l hl).toIdeal from le_sup_left)

theorem linearFormQuotientMap_homogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) (d : ℤ)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (hx : x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I d) :
    linearFormQuotientMap I l hl x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (linearFormQuotientIdeal I l hl) d := by
  obtain ⟨f, hf, rfl⟩ := hx
  exact ⟨f, hf, rfl⟩

def linearFormScalar (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) →ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing R n] Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal :=
  algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Module.End (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)) l

theorem linearFormScalar_homogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) (d : ℤ)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (hx : x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I d) :
    linearFormScalar I l x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d + 1) := by
  have hl' : l ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (1 : ℤ) := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
    exact hl
  have h := SetLike.GradedSMul.smul_mem hl' hx
  change l • x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (1 + d) at h
  change l • x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d + 1)
  simpa only [add_comm 1 d] using h

theorem linearFormScalar_injective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, l * f ∈ I.toIdeal → f ∈ I.toIdeal) :
    Function.Injective (linearFormScalar I l) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : linearFormScalar I l (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (x - y)
  rw [← hf] at hz ⊢
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hreg f
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

theorem linearFormQuotient_exact (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1) :
    Function.Exact (linearFormScalar I l) (linearFormQuotientMap I l hl) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hf
    have hf' : f ∈ I.toIdeal ⊔ Ideal.span {l} := Ideal.Quotient.eq_zero_iff_mem.mp hf
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hf'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
    refine ⟨Ideal.Quotient.mk I.toIdeal c, ?_⟩
    change Ideal.Quotient.mk I.toIdeal (l * c) = Ideal.Quotient.mk I.toIdeal f
    rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (linearFormQuotientIdeal I l hl).toIdeal (l * g) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mul_mem_right
    exact (le_sup_right : Ideal.span {l} ≤ I.toIdeal ⊔ Ideal.span {l}) (Ideal.subset_span rfl)

theorem coordinate_cech_exact_of_regular_linearForm [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hl : l.IsHomogeneous 1)
    (hreg : ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, l * f ∈ I.toIdeal → f ∈ I.toIdeal)
    (D : ℤ) (hquot : ∀ d : ℤ, D ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (linearFormQuotientIdeal I l hl).toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (linearFormQuotientIdeal I l hl)) d q) :
    ∀ d : ℤ, D ≤ d → ∀ q : ℕ, Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1))
      R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q :=
  RegularQuotientCech.ProjectiveCech.moduleCech_exact_of_regular_quotient (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (linearFormQuotientIdeal I l hl))
    (linearFormScalar I l) (linearFormQuotientMap I l hl)
    (linearFormScalar_homogeneous I l hl) (linearFormQuotientMap_homogeneous I l hl)
    (linearFormScalar_injective I l hreg) (linearFormQuotientMap_surjective I l hl)
    (linearFormQuotient_exact I l hl) D hquot

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormQuotient.GradedHilbert
