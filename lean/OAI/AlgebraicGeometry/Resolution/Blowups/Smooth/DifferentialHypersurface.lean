import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Derivation.Basic

/-! # Differential Hypersurface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface.Construction

noncomputable section

/-! Smooth hypersurfaces cut out by a function admitting a unit derivative. -/

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- The first-order correction of an algebra homomorphism along a derivation.
The correction is multiplicative because its coefficient is square zero. -/
def squareZeroDerivationCorrection (f : A →ₐ[k] B) (D : Derivation k A A)
    (c : B) (hc : c * c = 0) : A →ₐ[k] B where
  toFun a := f a - c * f (D a)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [map_add]; ring
  map_mul' a b := by
    simp only [D.leibniz, smul_eq_mul, map_add, map_mul]
    have hz : c * c * (f (D a) * f (D b)) = 0 := by rw [hc, zero_mul]
    linear_combination -hz
  commutes' r := by simp

/-- A function with derivative one cuts out a formally smooth hypersurface
in a formally smooth algebra. A square-zero lift is corrected to kill the function. -/
theorem formallySmooth_quotient_of_derivation_one [Algebra.FormallySmooth k A]
    (D : Derivation k A A) (z : A) (hDz : D z = 1) :
    Algebra.FormallySmooth k (A ⧸ Ideal.span {z}) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI g
  let J : Ideal A := Ideal.span {z}
  let π := Ideal.Quotient.mkₐ k J
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.comp_surjective k A I hI (g.comp π)
  have hfz : f z ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := AlgHom.congr_fun hf z
    have hz : π z = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton z))
    change Ideal.Quotient.mk I (f z) = g (π z) at h
    rw [hz, map_zero] at h
    exact h
  have hsq : f z * f z = 0 := by
    have h := Ideal.mul_mem_mul hfz hfz
    rw [← pow_two, hI] at h
    exact h
  let f' := squareZeroDerivationCorrection f D (f z) hsq
  have hf'z : f' z = 0 := by
    change f z - f z * f (D z) = 0
    rw [hDz, map_one, mul_one, sub_self]
  have hker : J ≤ RingHom.ker f'.toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hf'z
  let g' : A ⧸ J →ₐ[k] B := Ideal.Quotient.liftₐ J f' hker
  refine ⟨g', ?_⟩
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk I (f a - f z * f (D a)) = g (Ideal.Quotient.mk J a)
  rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hfz, zero_mul, sub_zero]
  exact AlgHom.congr_fun hf a

/-- Finite presentation upgrades the infinitesimal lifting result to smoothness. -/
theorem smooth_quotient_of_derivation_one [Algebra.Smooth k A]
    (D : Derivation k A A) (z : A) (hDz : D z = 1) :
    Algebra.Smooth k (A ⧸ Ideal.span {z}) := by
  let : Algebra.FormallySmooth k (A ⧸ Ideal.span {z}) :=
    formallySmooth_quotient_of_derivation_one D z hDz
  let : Algebra.FinitePresentation k (A ⧸ Ideal.span {z}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton z)
  exact ⟨inferInstance, inferInstance⟩

/-- A unit derivative can be normalized to one, so the same smoothness
criterion applies on any open set where a derivative is invertible. -/
theorem smooth_quotient_of_unit_derivative [Algebra.Smooth k A]
    (D : Derivation k A A) (z : A) (hDz : IsUnit (D z)) :
    Algebra.Smooth k (A ⧸ Ideal.span {z}) := by
  obtain ⟨u, hu⟩ := hDz
  apply smooth_quotient_of_derivation_one ((u⁻¹ : Aˣ) • D) z
  change (u⁻¹ : Aˣ) • D z = 1
  rw [← hu]
  exact Units.inv_mul u

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface.Construction
