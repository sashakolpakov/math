import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientMaps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Scalar Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarExtension.GradedHilbert

noncomputable section

/-!
Polynomial ideals under extension of the coefficient field. Expanding
coefficients in a vector-space basis proves the ideal-membership criterion
and shows that homogeneous saturation is preserved by field extension.
-/

open _root_.MvPolynomial _root_.Module

universe u v w

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {n : ℕ}

def basisCoefficientSupport {ι : Type w} (b : Basis ι K L) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) : Finset ι := by
  classical
  exact f.support.biUnion (fun a => (b.repr (f.coeff a)).support)

theorem support_repr_coeff_subset {ι : Type w} (b : Basis ι K L) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n)
    (a : Fin (n + 1) →₀ ℕ) : (b.repr (f.coeff a)).support ⊆ basisCoefficientSupport b f := by
  classical
  intro i hi
  by_cases ha : a ∈ f.support
  · exact Finset.mem_biUnion.mpr ⟨a, ha, hi⟩
  · have hz := notMem_support_iff.mp ha
    simp only [hz, map_zero, Finsupp.support_zero, Finset.notMem_empty] at hi

theorem polynomial_basis_expansion {ι : Type w} (b : Basis ι K L) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) :
    f = ∑ i ∈ basisCoefficientSupport b f,
      b i • MvPolynomial.map (algebraMap K L) (CoefficientMaps.GradedHilbert.coefficientApply (b.coord i) f) := by
  classical
  apply MvPolynomial.ext
  intro a
  simp only [coeff_sum, coeff_smul, coeff_map, CoefficientMaps.GradedHilbert.coeff_coefficientApply, Basis.coord_apply]
  have heq : (∑ i ∈ (b.repr (f.coeff a)).support, b.repr (f.coeff a) i • b i) =
      ∑ i ∈ basisCoefficientSupport b f, b.repr (f.coeff a) i • b i := by
    apply Finset.sum_subset (support_repr_coeff_subset b f a)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
  have hr := b.linearCombination_repr (f.coeff a)
  rw [Finsupp.linearCombination_apply, Finsupp.sum, heq] at hr
  simpa [Algebra.smul_def, mul_comm] using hr.symm

theorem mem_scalarExtendedIdeal_iff (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) :
    f ∈ CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I ↔ ∀ φ : L →ₗ[K] K, CoefficientMaps.GradedHilbert.coefficientApply φ f ∈ I := by
  constructor
  · intro hf φ
    exact CoefficientMaps.GradedHilbert.coefficientApply_mem_of_mem_scalarExtendedIdeal I φ hf
  · intro hf
    let b := Basis.ofVectorSpace K L
    rw [polynomial_basis_expansion b f]
    apply (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I).sum_mem
    intro i _
    apply ((CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I).restrictScalars L).smul_mem
    exact Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap K L)) (hf (b.coord i))

theorem map_mem_scalarExtendedIdeal_iff (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    MvPolynomial.map (algebraMap K L) f ∈ CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I ↔ f ∈ I := by
  constructor
  · intro hf
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (show (1 : L) ≠ 0 from one_ne_zero)
    have h := CoefficientMaps.GradedHilbert.coefficientApply_mem_of_mem_scalarExtendedIdeal I φ hf
    rwa [CoefficientMaps.GradedHilbert.coefficientApply_map, hφ, one_smul] at h
  · exact Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap K L))

theorem scalarExtendedIdeal_isHomogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) :
    (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal).IsHomogeneous (Hilbert.Polynomial.GradedHilbert.grading L n) := by
  obtain ⟨N, B, hB, hhom⟩ := GroebnerGenerators.GradedHilbert.exists_finite_homogeneous_generators MonomialOrder.lex I
  unfold CoefficientMaps.GradedHilbert.scalarExtendedIdeal
  rw [hB, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨_, d, _, hd⟩ := hhom b hb
  exact ⟨d, hd.map (algebraMap K L)⟩

def scalarExtendedHomogeneousIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading L n) :=
  ⟨CoefficientMaps.GradedHilbert.scalarExtendedIdeal I.toIdeal, scalarExtendedIdeal_isHomogeneous I⟩

theorem scalarExtendedIdeal_isSaturated (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I) := by
  intro f d hf hmul
  apply (mem_scalarExtendedIdeal_iff I f).mpr
  intro φ
  apply hI (CoefficientMaps.GradedHilbert.coefficientApply φ f) d (CoefficientMaps.GradedHilbert.coefficientApply_homogeneous φ hf)
  obtain ⟨m, hm⟩ := hmul
  refine ⟨m, fun g hg => ?_⟩
  have h := CoefficientMaps.GradedHilbert.coefficientApply_mem_of_mem_scalarExtendedIdeal I φ
    (hm (MvPolynomial.map (algebraMap K L) g) (hg.map (algebraMap K L)))
  rwa [CoefficientMaps.GradedHilbert.coefficientApply_map_mul] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarExtension.GradedHilbert
