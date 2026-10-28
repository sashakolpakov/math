import OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldBound
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Coefficient Maps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientMaps.GradedHilbert

noncomputable section

/-!
Applying a linear functional to polynomial coefficients. These maps
preserve homogeneous degrees and commute with multiplication by a
polynomial defined over the smaller coefficient field.
-/

open _root_.MvPolynomial _root_.Module

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {n : ℕ}

def coefficientApply (φ : L →ₗ[K] K) : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n →ₗ[K] Hilbert.Polynomial.GradedHilbert.CoordinateRing K n :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem coeff_coefficientApply (φ : L →ₗ[K] K) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n)
    (a : Fin (n + 1) →₀ ℕ) : (coefficientApply φ f).coeff a = φ (f.coeff a) := rfl

theorem support_coefficientApply_subset (φ : L →ₗ[K] K) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) :
    (coefficientApply φ f).support ⊆ f.support := by
  intro a ha
  rw [mem_support_iff, coeff_coefficientApply] at ha
  apply mem_support_iff.mpr
  intro hzero
  exact ha (hzero ▸ map_zero φ)

theorem coefficientApply_homogeneous (φ : L →ₗ[K] K)
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n} {d : ℕ} (hf : f.IsHomogeneous d) :
    (coefficientApply φ f).IsHomogeneous d := by
  apply (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support _ d).mpr
  intro a ha
  exact (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a (support_coefficientApply_subset φ f ha)

theorem coefficientApply_homogeneousComponent (φ : L →ₗ[K] K)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) (d : ℕ) :
    coefficientApply φ (homogeneousComponent d f) = homogeneousComponent d (coefficientApply φ f) := by
  classical
  apply MvPolynomial.ext
  intro a
  simp only [coeff_coefficientApply, coeff_homogeneousComponent]
  by_cases h : a.degree = d <;> simp [h]

theorem coefficientApply_mul_map (φ : L →ₗ[K] K)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) (g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    coefficientApply φ (f * MvPolynomial.map (algebraMap K L) g) = coefficientApply φ f * g := by
  classical
  apply MvPolynomial.ext
  intro a
  simp only [coeff_coefficientApply, coeff_mul, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm (f.coeff b.1), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem coefficientApply_map_mul (φ : L →ₗ[K] K)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (g : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) :
    coefficientApply φ (MvPolynomial.map (algebraMap K L) f * g) = f * coefficientApply φ g := by
  rw [mul_comm, coefficientApply_mul_map, mul_comm]

theorem coefficientApply_map (φ : L →ₗ[K] K) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    coefficientApply φ (MvPolynomial.map (algebraMap K L) f) = φ 1 • f := by
  apply MvPolynomial.ext
  intro a
  rw [coeff_coefficientApply, coeff_map, coeff_smul]
  have h := map_smul φ (f.coeff a) (1 : L)
  simpa [Algebra.smul_def, mul_comm] using h

def scalarExtendedIdeal (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) :=
  I.map (MvPolynomial.map (algebraMap K L))

theorem coefficientApply_mem_of_mem_scalarExtendedIdeal
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (φ : L →ₗ[K] K) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n}
    (hf : f ∈ scalarExtendedIdeal (L := L) I) : coefficientApply φ f ∈ I := by
  classical
  change f ∈ Submodule.span (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n)
    ((MvPolynomial.map (algebraMap K L)) '' (I : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) at hf
  obtain ⟨g, hg, hgf⟩ := (Finsupp.mem_span_image_iff_linearCombination (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n)).mp hf
  rw [← hgf, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply I.sum_mem
  intro a ha
  change coefficientApply φ (g a * MvPolynomial.map (algebraMap K L) a) ∈ I
  rw [coefficientApply_mul_map]
  exact I.mul_mem_left _ (hg ha)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientMaps.GradedHilbert
