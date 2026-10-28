import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary

/-! # Logarithmic Coordinate Generators -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinateGenerators.Construction

noncomputable section

/-! Finite coordinate generators for the logarithmic differential ideal on an étale chart. -/

variable {σ k R : Type*} [Field k] [CommRing R] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]

def etaleLogarithmicPartial (B : Finset σ) (i : σ) : Derivation k R R :=
  (if i ∈ B then algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) else 1) •
    Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i

omit [Fintype σ] in
theorem etaleLogarithmicPartial_logarithmic (B : Finset σ) (i : σ) :
    etaleLogarithmicPartial (k := k) (R := R) B i ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun j : B => algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) := by
  intro j
  change (if i ∈ B then algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) else 1) *
    Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i
      (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) ∈ _
  rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X]
  by_cases hij : i = j.val
  · subst i
    rw [ite_eq_left rfl, ite_eq_left j.property, mul_one]
    exact Ideal.mem_span_singleton_self _
  · rw [ite_eq_right hij, mul_zero]
    exact Ideal.zero_mem _

theorem firstRelativeLogarithmicDifferentialIdeal_coordinate_generators
    (B : Finset σ) (J : Ideal R) :
    Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k
      (fun j : B => algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) J =
      J ⊔ Ideal.span (Set.range (fun t : σ × J => etaleLogarithmicPartial (k := k) B t.1 t.2.val)) := by
  let L := J ⊔ Ideal.span (Set.range (fun t : σ × J => etaleLogarithmicPartial (k := k) B t.1 t.2.val))
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, p⟩, rfl⟩
    change D.val p.val ∈ L
    rw [Blowups.Etale.ModuleDerivations.Construction.etale_relative_derivation_apply (σ := σ)]
    apply Ideal.sum_mem
    intro i _
    have hi : etaleLogarithmicPartial (k := k) B i p.val ∈ L :=
      Submodule.mem_sup_right (Ideal.subset_span ⟨⟨i, p⟩, rfl⟩)
    by_cases hB : i ∈ B
    · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (D.property ⟨i, hB⟩)
      change D.val (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) =
        algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) * r at hr
      rw [hr]
      have he : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) * r *
          Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i p.val =
          r * etaleLogarithmicPartial (k := k) B i p.val := by
        simp only [etaleLogarithmicPartial, ite_eq_left hB, Derivation.smul_apply, smul_eq_mul]
        ring
      rw [he]
      exact L.mul_mem_left r hi
    · have he : etaleLogarithmicPartial (k := k) B i p.val =
          Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i p.val := by
        simp only [etaleLogarithmicPartial, ite_eq_right hB, one_smul]
      rw [he] at hi
      exact L.mul_mem_left _ hi
  · apply sup_le (Relative.LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k _ J)
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, p⟩, rfl⟩
    exact Relative.LogarithmicIdeal.Construction.relative_logarithmic_derivation_mem_first k _ J
      ⟨_, etaleLogarithmicPartial_logarithmic B i⟩ p.property

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinateGenerators.Construction
