import OAI.AlgebraicGeometry.Resolution.Blowups.LocalCoordinatePrime
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorUniqueness
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Boundary Factor Uniqueness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryFactorUniqueness.Construction

noncomputable section

/-! Canonical boundary exponents and residual ideals in actual étale local rings. -/

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S]
  [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Local boundary coordinates are regular, prime, and do not divide one
another. These are proved properties of the actual étale local ring. -/
theorem etale_local_boundary_factor_properties (B : Finset σ) (q : Ideal S) [q.IsMaximal]
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈ q) :
    let w := fun i : σ => algebraMap S (Localization.AtPrime q)
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))
    (∀ i ∈ B, IsRegular (w i)) ∧ (∀ i ∈ B, (Ideal.span {w i}).IsPrime) ∧
      ∀ i ∈ B, ∀ j ∈ B, j ≠ i → w j ∉ Ideal.span {w i} := by
  let T := Localization.AtPrime q
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  let : Algebra ℚ T := ((algebraMap (MvPolynomial σ K) T).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let w := fun i : σ => algebraMap S T (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))
  let D := fun i : σ => Derivation.Construction.extendEtaleRingDerivation (S := T)
    (LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) i)
  have hD : ∀ i j : σ, D i (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [show D i (w j) = algebraMap S T
      (LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) i
        (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j))) from
      Derivation.Construction.extendEtaleRingDerivation_algebraMap _ _, CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X]
    split_ifs <;> simp only [map_one, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    exact Coordinate.Regularity.Construction.coordinate_isRegular (D i) (w i) (by rw [hD, ite_eq_left rfl])
  · intro i hi
    exact LocalCoordinatePrime.Construction.etale_boundary_coordinate_atPrime_isPrime (K := K) i q (hB i hi)
  · intro i hi j _ hji
    let M := IsLocalRing.maximalIdeal T
    have hwi : w i ∈ M := by
      change algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈
        M.comap (algebraMap S T)
      change algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)).under S
      rw [Localization.AtPrime.under_maximalIdeal]
      exact hB i hi
    exact Boundary.FactorUniqueness.Construction.transverse_coordinate_not_mem_span (D j) (w i) (w j)
      (by rw [hD, ite_eq_right hji]) (by rw [hD, ite_eq_left rfl]) M
      (IsLocalRing.maximalIdeal.isMaximal T).ne_top hwi

/-- Two primitive local boundary factorizations have the same exponent
function and the same residual ideal. -/
theorem etale_local_boundary_factorization_unique (B : Finset σ) (q : Ideal S) [q.IsMaximal]
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈ q)
    (a b : σ → ℕ) (L M : Ideal (Localization.AtPrime q))
    (ha0 : ∀ i ∉ B, a i = 0) (hb0 : ∀ i ∉ B, b i = 0)
    (hL : ∀ i ∈ B, ¬ L ≤ Ideal.span {algebraMap S (Localization.AtPrime q)
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))})
    (hM : ∀ i ∈ B, ¬ M ≤ Ideal.span {algebraMap S (Localization.AtPrime q)
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))})
    (he : Ideal.span {∏ i ∈ B, (algebraMap S (Localization.AtPrime q)
          (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))) ^ a i} * L =
        Ideal.span {∏ i ∈ B, (algebraMap S (Localization.AtPrime q)
          (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))) ^ b i} * M) : a = b ∧ L = M := by
  obtain ⟨hreg, hprime, hind⟩ := etale_local_boundary_factor_properties (K := K) B q hB
  have hab := Boundary.FactorUniqueness.Construction.finite_prime_boundary_exponents_unique B _ a b L M hreg hprime hind hL hM he
  refine ⟨?_, Boundary.FactorUniqueness.Construction.finite_regular_boundary_residual_unique B _ a b L M hreg hab he⟩
  funext i
  by_cases hi : i ∈ B
  · exact hab i hi
  · rw [ha0 i hi, hb0 i hi]

/-- Every nonzero ideal of the actual local ring has a unique primitive
boundary factorization with exponents zero off the retained boundary. -/
theorem existsUnique_etale_local_boundary_factorization
    (B : Finset σ) (q : Ideal S) [q.IsMaximal]
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈ q)
    (J : Ideal (Localization.AtPrime q)) (hJ : J ≠ ⊥) :
    let w := fun i : σ => algebraMap S (Localization.AtPrime q)
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))
    ∃! v : (σ → ℕ) × Ideal (Localization.AtPrime q),
      (∀ i ∉ B, v.1 i = 0) ∧ J = Ideal.span {∏ i ∈ B, w i ^ v.1 i} * v.2 ∧
        ∀ i ∈ B, ¬ v.2 ≤ Ideal.span {w i} := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  let w := fun i : σ => algebraMap S (Localization.AtPrime q)
    (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))
  obtain ⟨_, hprime, _⟩ := etale_local_boundary_factor_properties (K := K) B q hB
  obtain ⟨a, L, ha0, hfactor, _, _, hL⟩ := Boundary.FactorExtraction.Construction.exists_finite_boundary_factorization B w
    (fun i hi => (hprime i hi).ne_top) J hJ
  refine ⟨(a, L), ⟨ha0, hfactor, hL⟩, ?_⟩
  rintro ⟨b, M⟩ ⟨hb0, hfactor', hM⟩
  obtain ⟨hab, hLM⟩ := etale_local_boundary_factorization_unique (K := K) B q hB b a M L
    hb0 ha0 hM hL (hfactor'.symm.trans hfactor)
  exact Prod.ext hab hLM

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryFactorUniqueness.Construction
