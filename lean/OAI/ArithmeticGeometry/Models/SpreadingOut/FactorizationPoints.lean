import OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationAlgebra

/-! # Factorization Points -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationPoints.Construction.PolynomialFactorization

noncomputable section

/-! Bounded nonconstant factorizations give points of the parameter algebra. -/

open _root_.MvPolynomial

universe u

def coefficientsOfFactors {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {n d : ℕ} (q : Fin 2 → MvPolynomial (Fin n) k) (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d) :
    FactorizationAlgebra.Construction.PolynomialFactorization.Coefficients R n d →ₐ[R] k :=
  MvPolynomial.aeval (Sum.elim
    (fun v : Fin 2 × BoundedPolynomial.Construction.PolynomialBox n d ↦ (q v.1).coeff (BoundedPolynomial.Construction.polynomialBoxExponent v.2))
    (fun i : Fin 2 ↦ ((q i).coeff (BoundedPolynomial.Construction.polynomialBoxExponent (w i)))⁻¹))

theorem universalFactor_map_of_factors {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {n d : ℕ} (q : Fin 2 → MvPolynomial (Fin n) k) (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d)
    (hq : ∀ i, (q i).totalDegree ≤ d) (i : Fin 2) :
    MvPolynomial.map (coefficientsOfFactors (R := R) q w).toRingHom (FactorizationAlgebra.Construction.PolynomialFactorization.universalFactor R n d i) = q i := by
  rw [FactorizationAlgebra.Construction.PolynomialFactorization.universalFactor, BoundedPolynomial.Construction.boundedPolynomial_map]
  convert BoundedPolynomial.Construction.boundedPolynomial_reconstruct (q i) (hq i) using 1
  congr 1
  funext v
  exact aeval_X _ _

theorem factor_relations_vanish {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {n d : ℕ} (p : MvPolynomial (Fin n) R) (q : Fin 2 → MvPolynomial (Fin n) k)
    (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d) (hq : ∀ i, (q i).totalDegree ≤ d)
    (hprod : MvPolynomial.map (algebraMap R k) p = q 0 * q 1)
    (hw : ∀ i, (q i).coeff (BoundedPolynomial.Construction.polynomialBoxExponent (w i)) ≠ 0)
    {r : FactorizationAlgebra.Construction.PolynomialFactorization.Coefficients R n d} (hr : r ∈ FactorizationAlgebra.Construction.PolynomialFactorization.relations p d w) :
    coefficientsOfFactors (R := R) q w r = 0 := by
  let ψ := coefficientsOfFactors (R := R) q w
  have hp : MvPolynomial.map ψ.toRingHom
      (MvPolynomial.map (algebraMap R (FactorizationAlgebra.Construction.PolynomialFactorization.Coefficients R n d)) p) = MvPolynomial.map (algebraMap R k) p := by
    rw [map_map]
    exact congrArg (fun f : R →+* k ↦ MvPolynomial.map f p) ψ.comp_algebraMap
  rcases hr with ⟨m, rfl⟩ | ⟨i, rfl⟩
  · have he : MvPolynomial.map ψ.toRingHom (FactorizationAlgebra.Construction.PolynomialFactorization.discrepancy p d) = 0 := by
      rw [FactorizationAlgebra.Construction.PolynomialFactorization.discrepancy, map_sub, map_mul, hp,
        universalFactor_map_of_factors q w hq, universalFactor_map_of_factors q w hq, hprod, sub_self]
    have hc := congrArg (fun p : MvPolynomial (Fin n) k ↦ p.coeff m) he
    rw [coeff_map, AddMonoidAlgebra.coeff_zero] at hc
    exact hc
  · simp [coefficientsOfFactors, hw i]

theorem nonempty_of_factorization {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {n d : ℕ} (p : MvPolynomial (Fin n) R) (q : Fin 2 → MvPolynomial (Fin n) k)
    (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d) (hq : ∀ i, (q i).totalDegree ≤ d)
    (hprod : MvPolynomial.map (algebraMap R k) p = q 0 * q 1)
    (hw : ∀ i, (q i).coeff (BoundedPolynomial.Construction.polynomialBoxExponent (w i)) ≠ 0) :
    Nonempty (FactorizationAlgebra.Construction.PolynomialFactorization.ParameterAlgebra p d w →ₐ[R] k) := by
  let ψ := coefficientsOfFactors (R := R) q w
  have hI : FactorizationAlgebra.Construction.PolynomialFactorization.ideal p d w ≤ RingHom.ker ψ.toRingHom :=
    Ideal.span_le.mpr (fun r hr ↦ factor_relations_vanish p q w hq hprod hw hr)
  exact ⟨Ideal.Quotient.liftₐ (FactorizationAlgebra.Construction.PolynomialFactorization.ideal p d w) ψ (fun r hr ↦ hI hr)⟩

theorem parameter_algebra_killed_by_nonzero
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {n d : ℕ} (p : MvPolynomial (Fin n) R) (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d)
    (hw : ∀ i, BoundedPolynomial.Construction.polynomialBoxExponent (w i) ≠ 0)
    (hp : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure K)) p)) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R (FactorizationAlgebra.Construction.PolynomialFactorization.ParameterAlgebra p d w) r = 0 :=
  AlgebraicSpecialization.Construction.finiteType_no_geometric_generic_point_killed_by_nonzero R K (FactorizationAlgebra.Construction.PolynomialFactorization.ParameterAlgebra p d w)
    (FactorizationAlgebra.Construction.PolynomialFactorization.no_points_of_irreducible hw hp)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationPoints.Construction.PolynomialFactorization
