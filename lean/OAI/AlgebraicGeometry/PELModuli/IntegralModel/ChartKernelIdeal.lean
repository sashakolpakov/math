import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # Chart Kernel Ideal -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChartKernelIdeal.PolarizationEmbedding

noncomputable section

/-! A homogeneous ideal from actual ring-valued chart restrictions.
When the distinguished variable is a unit on each chart, this ideal is
saturated with respect to the irrelevant ideal. -/

open _root_.MvPolynomial

universe u v
variable {R : Type u} [CommRing R] {σ : Type v}
  {A : σ → Type u} [∀ i, CommRing (A i)]
  (φ : ∀ i, MvPolynomial σ R →+* A i) (J : ∀ i, Ideal (A i))
attribute [local instance] MvPolynomial.gradedAlgebra

def chartKernelIdeal : HomogeneousIdeal (homogeneousSubmodule σ R) :=
  (⨅ i, (J i).comap (φ i)).homogeneousCore (homogeneousSubmodule σ R)

theorem mem_chartKernelIdeal {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    p ∈ (chartKernelIdeal φ J).toIdeal ↔ ∀ i, φ i p ∈ J i := by
  constructor
  · intro h
    have h' := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule σ R)
      (⨅ i, (J i).comap (φ i)) h
    simpa only [Ideal.mem_iInf, Ideal.mem_comap] using h'
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hp⟩
      (by simpa only [Ideal.mem_iInf, Ideal.mem_comap] using h)

theorem chartKernelIdeal_saturated (hφ : ∀ i, IsUnit (φ i (X i)))
    (p : MvPolynomial σ R) (d : ℕ) (hp : p.IsHomogeneous d)
    (h : ∃ m : ℕ, ∀ q : MvPolynomial σ R, q.IsHomogeneous m →
      q * p ∈ (chartKernelIdeal φ J).toIdeal) :
    p ∈ (chartKernelIdeal φ J).toIdeal := by
  obtain ⟨m, hm⟩ := h
  apply (mem_chartKernelIdeal φ J hp).mpr
  intro i
  have hX : (X (R := R) i ^ m).IsHomogeneous m := by
    simpa only [one_mul] using (isHomogeneous_X R i).pow m
  have hi := (mem_chartKernelIdeal φ J (hX.mul hp)).mp (hm _ hX) i
  rw [map_mul, map_pow] at hi
  exact ((J i).unit_mul_mem_iff_mem ((hφ i).pow m)).mp hi

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChartKernelIdeal.PolarizationEmbedding
