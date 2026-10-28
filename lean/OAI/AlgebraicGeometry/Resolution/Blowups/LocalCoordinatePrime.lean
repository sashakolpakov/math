import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalDomain

/-! # Local Coordinate Prime -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalCoordinatePrime.Construction

noncomputable section

/-! Coordinate-center ideals are prime in the actual ambient local rings. -/

section

variable {R : Type*} [CommRing R]

/-- Localizing the ambient ring and then quotienting gives the same
localization as quotienting first. A domain local quotient therefore makes
the extended center ideal prime in the ambient local ring. -/
theorem ideal_map_atPrime_isPrime_of_local_quotient_domain
    (I q : Ideal R) [q.IsMaximal] (hI : I ≤ q)
    [(q.map (Ideal.Quotient.mk I)).IsPrime]
    [IsDomain (Localization.AtPrime (q.map (Ideal.Quotient.mk I)))] :
    (I.map (algebraMap R (Localization.AtPrime q))).IsPrime := by
  let A := R ⧸ I
  let Q : Ideal A := q.map (Ideal.Quotient.mk I)
  let : Q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let B := Localization.AtPrime q ⧸ I.map (algebraMap R (Localization.AtPrime q))
  have hQ : Q.comap (Ideal.Quotient.mk I) = q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]
  have hM : Algebra.algebraMapSubmonoid A q.primeCompl = Q.primeCompl := by
    change q.primeCompl.map (Ideal.Quotient.mk I) = Q.primeCompl
    have h := Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q
    simpa only [hQ] using h
  let : IsLocalization.AtPrime B Q := by
    change IsLocalization Q.primeCompl B
    rw [← hM]
    infer_instance
  let e := IsLocalization.algEquiv Q.primeCompl B (Localization.AtPrime Q)
  have hB : IsDomain B := e.injective.isDomain e.toRingHom
  exact (Ideal.Quotient.isDomain_iff_prime _).mp hB

end

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Every coordinate-center ideal is prime at each closed point of the center. -/
theorem etale_coordinate_center_ideal_atPrime_isPrime (C : Finset σ) (q : Ideal S)
    [q.IsMaximal]
    (hC : ∀ i ∈ C, algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈ q) :
    (((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)).map
      (algebraMap S (Localization.AtPrime q))).IsPrime := by
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
  have hI : I ≤ q := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hC i hi
  let Q := q.map (Ideal.Quotient.mk I)
  let : Q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let : IsDomain (Localization.AtPrime Q) :=
    Blowups.Etale.LocalDomain.Construction.etale_coordinate_center_localRing_isDomain (K := K) C Q
  exact ideal_map_atPrime_isPrime_of_local_quotient_domain I q hI

/-- In particular, each boundary coordinate through a closed point generates
a prime ideal of the ambient local ring. -/
theorem etale_boundary_coordinate_atPrime_isPrime (i : σ) (q : Ideal S) [q.IsMaximal]
    (hi : algebraMap (MvPolynomial σ K) S (MvPolynomial.X i) ∈ q) :
    (Ideal.span {algebraMap S (Localization.AtPrime q)
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))}).IsPrime := by
  have h := etale_coordinate_center_ideal_atPrime_isPrime (K := K) ({i} : Finset σ) q
    (by intro j hj; simpa only [Finset.mem_singleton.mp hj] using hi)
  simpa only [Blowups.Etale.CoordinateHypersurfaceMap.Construction.singleton_coordinate_extended_ideal, Ideal.map_span, Set.image_singleton] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalCoordinatePrime.Construction
