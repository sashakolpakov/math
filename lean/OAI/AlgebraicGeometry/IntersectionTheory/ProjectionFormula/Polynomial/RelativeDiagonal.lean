import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DiagonalParameters
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.TensorKernel

/-! # Relative Diagonal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.RelativeDiagonal

noncomputable section

/-! The kernel of passing from the ground-field product to the product
over polynomial coordinates is precisely the ideal of coordinate
differences. This is an equality of native tensor-product ideals. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

open _root_.MvPolynomial OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DiagonalParameters

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
  (σ : Type) [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]

local notation "φ" => IsScalarTower.toAlgHom K (MvPolynomial σ K) A

def map : A ⊗[K] A →ₐ[A] A ⊗[MvPolynomial σ K] A :=
  Relative.TensorKernel.map K (MvPolynomial σ K) A

def ideal : Ideal (A ⊗[K] A) := Ideal.span (Set.range (Smooth.DiagonalParameters.parameter K A σ φ))

theorem all_differences (p : MvPolynomial σ K) :
    φ p ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ p ∈ ideal K A σ := by
  let J := ideal K A σ
  let q := Ideal.Quotient.mkₐ K J
  let l := q.comp ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).comp φ)
  let r := q.comp ((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).comp φ)
  have he : l = r := by
    ext i
    apply sub_eq_zero.mp
    change q (φ (X i) ⊗ₜ[K] (1 : A)) - q ((1 : A) ⊗ₜ[K] φ (X i)) = 0
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have h : Smooth.DiagonalParameters.parameter K A σ φ i ∈ J := Ideal.subset_span ⟨i, rfl⟩
    simpa only [Smooth.DiagonalParameters.parameter, neg_sub] using J.neg_mem h
  apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
  change q (φ p ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ p) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun he p)

theorem kernel : RingHom.ker (map K A σ).toRingHom = ideal K A σ := by
  apply le_antisymm
  · exact Relative.TensorKernel.kernel_le K (MvPolynomial σ K) A (ideal K A σ)
      (all_differences K A σ)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (1 : A) ⊗ₜ[MvPolynomial σ K] φ (X i) - φ (X i) ⊗ₜ[MvPolynomial σ K] (1 : A) = 0
    have h := TensorProduct.tmul_smul (R := MvPolynomial σ K) (X (R := K) i) (1 : A) (1 : A)
    rw [TensorProduct.smul_tmul'] at h
    simp only [Algebra.smul_def] at h
    change (1 : A) ⊗ₜ[MvPolynomial σ K] (φ (X i) * 1) = (φ (X i) * 1) ⊗ₜ[MvPolynomial σ K] (1 : A) at h
    simpa only [mul_one] using sub_eq_zero.mpr h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.RelativeDiagonal
