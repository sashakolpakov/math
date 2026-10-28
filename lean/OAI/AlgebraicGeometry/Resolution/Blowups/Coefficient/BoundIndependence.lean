import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentSupport
import OAI.AlgebraicGeometry.Resolution.Blowups.TwoTransverseEquationComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface

/-! # Bound Independence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.BoundIndependence.Construction

noncomputable section

/-! Differential bounds for homogenized coefficient ideals do not depend on the normal equation, in arbitrary dimension. -/

universe u

theorem coefficient_bound_of_other_normal
    {σ k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra ℚ R]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]
    (J : Ideal R) (n m : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ := by
  let : Algebra.Smooth k (MvPolynomial σ k) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k R := Algebra.Smooth.comp k (MvPolynomial σ k) R
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (R ⧸ Ideal.span {t}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E t hE
  let H := Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
  let I := TangentNaturality.Construction.coefficientTangentCenter k z H (n + 1) m
  let L := TangentNaturality.Construction.coefficientTangentCenter k t H (n + 1) m
  have hI : I = ⊤ := by
    change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z H (n + 1)) m).comap _ = ⊤
    rw [hbound, Ideal.comap_top]
  by_contra hnot
  have hL : L ≠ ⊤ := by
    intro he
    apply hnot
    have hq := TangentNaturality.Construction.coefficientTangentCenter_quotient k t H (n + 1) m
    change L.map (Ideal.Quotient.mk (Ideal.span {t})) = _ at hq
    rw [he, Ideal.map_top] at hq
    exact hq.symm
  obtain ⟨q, hq, hLq⟩ := Ideal.exists_le_maximal L hL
  let : q.IsMaximal := hq
  have hT : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ q := by
    have h := TangentSupport.Construction.relative_tangent_le_of_coefficient_tangent_center_le_prime k t H n m q hLq
    rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent] at h
  let r : R →ₐ[k] q.ResidueField := IsScalarTower.toAlgHom k R q.ResidueField
  have htransz : ∃ i : σ, i ∉ (∅ : Finset σ) ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z) ≠ 0 := by
    apply Blowups.Etale.TransverseDirection.Construction.exists_transverse_partial_of_boundary_derivation ∅ D r z (by simp)
    rw [hD, map_one]
    exact one_ne_zero
  have htranst : ∃ i : σ, i ∉ (∅ : Finset σ) ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i t) ≠ 0 := by
    apply Blowups.Etale.TransverseDirection.Construction.exists_transverse_partial_of_boundary_derivation ∅ E r t (by simp)
    rw [hE, map_one]
    exact one_ne_zero
  have hrz : r z = 0 := Ideal.algebraMap_residueField_eq_zero.mpr (hT hz)
  have hrt : r t = 0 := Ideal.algebraMap_residueField_eq_zero.mpr (hT ht)
  obtain ⟨U, instU, instkU, f, g, v, hf, hg, heq, _, hH, _, hvg, _⟩ :=
    TwoTransverseEquationComparison.Construction.exists_two_transverse_equation_center_comparison J ∅ z t n r htransz htranst hz ht (hrz.trans hrt.symm)
  let : CommRing U := instU
  let : Algebra k U := instkU
  have hcoeff := Blowups.Etale.QuotientNaturality.Construction.relativeCoefficientIdeal_comparison_eq (σ := σ) f g hf hg z t heq H H hH (n + 1)
  have hIL : I.map f.toRingHom = L.map g.toRingHom :=
    TangentNaturality.Construction.coefficientTangentCenter_compared_ambient_ideals f g hf hg z t heq H H (n + 1) m hcoeff
  rw [hI, Ideal.map_top] at hIL
  let Q := RingHom.ker v.toRingHom
  let : Q.IsPrime := Ideal.comap_isPrime v.toRingHom ⊥
  have hle : L.map g.toRingHom ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change v (g x) = 0
    rw [hvg x]
    exact Ideal.algebraMap_residueField_eq_zero.mpr (hLq hx)
  rw [← hIL] at hle
  exact (inferInstance : Q.IsPrime).ne_top (top_le_iff.mp hle)

theorem coefficient_bound_independent_of_normal
    {σ k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra ℚ R]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]
    (J : Ideal R) (n m : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ ↔
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ :=
  ⟨coefficient_bound_of_other_normal (σ := σ) J n m z t D E hD hE hz ht,
    coefficient_bound_of_other_normal (σ := σ) J n m t z E D hE hD ht hz⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.BoundIndependence.Construction
