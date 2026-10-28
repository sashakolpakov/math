import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialZeroLocus
import Mathlib.Topology.ContinuousOn

/-! # Principal Open -/

namespace OAI.AlgebraicGeometry

/-!
# Principal open subsets of ordinary affine complex points

Nonvanishing loci of regular functions are open for the evaluation topology.
Their intersections and inverse images have the expected algebraic formulas.
Functions generating the unit ideal give an open cover, on which continuity
can be checked locally. These are genuine subsets of the complex-character
space, with its ordinary topology.
-/

universe u v w

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The principal open subset of complex characters where a regular function is nonzero. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a : A) : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := {x | x a ≠ 0}

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.mem_principalOpen (a : A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    x ∈ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a ↔ x a ≠ 0 := Iff.rfl

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen (a : A) : IsOpen (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_nonzeroSet a

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_zero : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (0 : A) = ∅ := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_one : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (1 : A) = Set.univ := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_mul (a b : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a * b) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a ∩ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_pow (a : A) {n : ℕ} (hn : n ≠ 0) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a ^ n) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen, hn]

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_neg (a : A) : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (-a) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := by
  ext x
  simp [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen]

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_add_subset (a b : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (a + b) ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a ∪ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b := by
  intro x hx
  by_contra h
  have hz : x a = 0 ∧ x b = 0 := by
    simpa only [Set.mem_union, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.mem_principalOpen, not_or, not_not] using h
  exact hx (by simp [hz.1, hz.2])

/-- Pullback of a principal open is the principal open of the pulled-back function. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_preimage_principalOpen {B : Type v} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (a : A) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) ⁻¹' Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (f a) := rfl

/-- Functions generating the unit ideal cannot all vanish at a complex point. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.exists_mem_principalOpen_of_span_eq_top {ι : Type v}
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ i, x ∈ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) := by
  by_contra h
  have hz : ∀ i, x (g i) = 0 := by
    simpa only [not_exists, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.mem_principalOpen, not_not] using h
  have hle : Ideal.span (Set.range g) ≤ RingHom.ker x.toRingHom := by
    apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    exact hz i
  have hone : (1 : A) ∈ RingHom.ker x.toRingHom := hle (by simp [hg])
  simp at hone

theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.iUnion_principalOpen_eq_univ {ι : Type v}
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) :
    (⋃ i, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.exists_mem_principalOpen_of_span_eq_top g hg x

/-- Continuity can be checked on a principal open cover from a unit-ideal generating family. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_principalOpen_cover {ι : Type v} {X : Type w} [TopologicalSpace X]
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) (F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → X) :
    Continuous F ↔ ∀ i, Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) => F x.1) := by
  constructor
  · intro h i
    exact h.comp continuous_subtype_val
  · intro h
    apply continuous_of_cover_nhds (s := fun i => Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i))
    · intro x
      obtain ⟨i, hi⟩ := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.exists_mem_principalOpen_of_span_eq_top g hg x
      exact ⟨i, (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen (g i)).mem_nhds hi⟩
    · intro i
      exact continuousOn_iff_continuous_domRestrict.mpr (h i)

end OAI.AlgebraicGeometry
