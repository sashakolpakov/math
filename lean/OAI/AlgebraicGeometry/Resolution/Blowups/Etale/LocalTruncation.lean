import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FiniteNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface
import Mathlib.RingTheory.Nullstellensatz

/-! # Local Truncation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalTruncation.Construction

noncomputable section

section

/-! Identical rational residue neighborhoods for étale coordinate algebras. -/

variable {K S : Type*} [Field K] [IsAlgClosed K] [CommRing S]

/-- The residue field of a closed point of a finite type algebra over
an algebraically closed field is exactly the coefficient field. -/
theorem finiteType_closed_residueField_bijective [Algebra K S] [Algebra.FiniteType K S]
    (q : Ideal S) [q.IsMaximal] : Function.Bijective (algebraMap K q.ResidueField) := by
  let : Algebra.FiniteType K q.ResidueField := Algebra.FiniteType.trans
    (R := K) (S := S) (A := q.ResidueField) inferInstance inferInstance
  let : Module.Finite K q.ResidueField := finite_of_finite_type_of_isJacobsonRing K q.ResidueField
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

variable {σ : Type*} [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- At a closed point over a rational polynomial point, the induced map
of first residue quotients is bijective. -/
theorem etale_local_residue_quotient_bijective (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] :
    Function.Bijective (algebraMap (MvPolynomial σ K ⧸ PolynomialTranslation.Construction.polynomialPointIdeal x)
      (Localization.AtPrime q ⧸ (PolynomialTranslation.Construction.polynomialPointIdeal x).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime q)))) := by
  let A := MvPolynomial σ K
  let T := Localization.AtPrime q
  let p := PolynomialTranslation.Construction.polynomialPointIdeal x
  let : Algebra K S := ((algebraMap A S).comp MvPolynomial.C).toAlgebra
  let : IsScalarTower K A S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType K S := Algebra.FiniteType.trans
    (R := K) (S := A) (A := S) inferInstance inferInstance
  let : p.IsMaximal := RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval x)
    (fun r => ⟨MvPolynomial.C r, MvPolynomial.eval_C r⟩)
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  have hM : p.map (algebraMap A T) = IsLocalRing.maximalIdeal T :=
    LocalCoordinates.Construction.etale_local_maximalIdeal_eq_map_point x q
  let : (p.map (algebraMap A T)).IsMaximal := hM.symm ▸ IsLocalRing.maximalIdeal.isMaximal T
  let : IsScalarTower K (A ⧸ p) (T ⧸ p.map (algebraMap A T)) := Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower p
  have hK : Function.Surjective (algebraMap K (T ⧸ p.map (algebraMap A T))) := by
    rw [hM]
    exact (finiteType_closed_residueField_bijective (K := K) q).2
  constructor
  · exact RingHom.injective _
  · rw [IsScalarTower.algebraMap_eq K (A ⧸ p) (T ⧸ p.map (algebraMap A T))] at hK
    intro y
    obtain ⟨r, hr⟩ := hK y
    exact ⟨algebraMap K (A ⧸ p) r, hr⟩

end

/-! Canonical finite Taylor neighborhoods of étale local coordinate rings. -/

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

theorem etale_local_truncation_bijective (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective (algebraMap (MvPolynomial σ K ⧸ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n)
      (Localization.AtPrime q ⧸ (PolynomialTranslation.Construction.polynomialPointIdeal x ^ n).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime q)))) := by
  let : Algebra.FormallyEtale S (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let : Algebra.FormallyEtale (MvPolynomial σ K) (Localization.AtPrime q) :=
    Algebra.FormallyEtale.comp (MvPolynomial σ K) S (Localization.AtPrime q)
  exact FiniteNeighborhood.Construction.formallyEtale_bijective_on_finite_neighborhood (PolynomialTranslation.Construction.polynomialPointIdeal x)
    (etale_local_residue_quotient_bijective x q) n hn

/-- The actual local ring and the polynomial coordinate ring have canonically
isomorphic quotients by every positive power of their point ideals. -/
def etaleLocalTruncationEquiv (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ) (hn : n ≠ 0) :
    (MvPolynomial σ K ⧸ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n) ≃+*
      (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) :=
  (RingEquiv.ofBijective _ (etale_local_truncation_bijective x q n hn)).trans
    (Ideal.quotEquivOfEq (by rw [Ideal.map_pow, LocalCoordinates.Construction.etale_local_maximalIdeal_eq_map_point x q]))

theorem etaleLocalTruncationEquiv_mk (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ) (hn : n ≠ 0) (p : MvPolynomial σ K) :
    etaleLocalTruncationEquiv x q n hn (Ideal.Quotient.mk (PolynomialTranslation.Construction.polynomialPointIdeal x ^ n) p) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n)
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime q) p) := rfl

/-- Polynomial order is reflected exactly by the local coordinate map. -/
theorem etale_local_polynomial_mem_pow_iff (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ) (hn : n ≠ 0) (p : MvPolynomial σ K) :
    algebraMap (MvPolynomial σ K) (Localization.AtPrime q) p ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n ↔ p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (etaleLocalTruncationEquiv x q n hn).injective
    rw [map_zero, etaleLocalTruncationEquiv_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← etaleLocalTruncationEquiv_mk x q n hn p,
      Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- Every local section admits a polynomial representative to any prescribed
finite order. This applies to sections that do not come from the polynomial base. -/
theorem etale_local_exists_polynomial_approximation (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ) (hn : n ≠ 0) (s : Localization.AtPrime q) :
    ∃ p : MvPolynomial σ K,
      s - algebraMap (MvPolynomial σ K) (Localization.AtPrime q) p ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n := by
  obtain ⟨p, hp⟩ := (etaleLocalTruncationEquiv x q n hn).surjective
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) s)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [etaleLocalTruncationEquiv_mk] at hp
  refine ⟨p, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, hp, sub_self]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalTruncation.Construction
