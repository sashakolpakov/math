import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalOrder

/-! # Tangent Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.TangentCriterion.Construction

noncomputable section

/-! Coordinate derivations detect nonzero cotangent vectors after an étale extension. -/

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.FormallyEtale A B] [Fintype ι] [DecidableEq ι]

/-- If a section belongs to the coordinate ideal and all its coordinate
derivatives belong to that ideal, then the section belongs to its square. -/
theorem mapped_coordinate_mem_square_of_derivatives
    (z : ι → A) (D : ι → Derivation ℤ A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (p : A)
    (hp : algebraMap A B p ∈ Ideal.span (Set.range (fun i => algebraMap A B (z i))))
    (hDp : ∀ i, algebraMap A B (D i p) ∈
      Ideal.span (Set.range (fun j => algebraMap A B (z j)))) :
    algebraMap A B p ∈ Ideal.span (Set.range (fun i => algebraMap A B (z i))) ^ 2 := by
  let w : ι → B := fun i => algebraMap A B (z i)
  let δ : ι → Derivation ℤ B B := fun i => Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := B) (D i)
  have hδ : ∀ i j, δ i (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD]
    split_ifs <;> simp
  let E := EulerOrderCriterion.Construction.coordinateEulerDerivation w δ
  let M := Ideal.span (Set.range w)
  have hE : E (algebraMap A B p) ∈ M ^ 2 := by
    rw [EulerOrderCriterion.Construction.coordinateEulerDerivation_apply]
    apply Ideal.sum_mem
    intro i _
    rw [pow_two, Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (hDp i)
  have hcong : E (algebraMap A B p) - algebraMap A B p ∈ M ^ 2 := by
    apply EulerOrderCriterion.Construction.euler_span_mod_square E (Set.range w) _ (EulerOrderCriterion.Construction.coordinateEulerDerivation_mem_span w δ) hp
    rintro x ⟨i, rfl⟩
    exact EulerOrderCriterion.Construction.coordinateEulerDerivation_coordinate w δ hδ i
  simpa only [sub_sub_cancel] using (M ^ 2).sub_mem hE hcong

variable {σ K S : Type*} [Field K] [CommRing S] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- A nonzero cotangent vector at a rational point has a nonvanishing
coordinate derivative already on the affine ring. -/
theorem etale_exists_coordinate_derivative_not_mem (x : σ → K)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (p : S) (hp : p ∈ q)
    (hp2 : algebraMap S (Localization.AtPrime q) p ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2) :
    ∃ i : σ, Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) i p ∉ q := by
  classical
  by_contra h
  push Not at h
  let T := Localization.AtPrime q
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let z : σ → S := Blowups.Etale.LocalOrder.Construction.etaleCenteredCoordinate x
  let D : σ → Derivation ℤ S S := Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K)
  have hM : Ideal.span (Set.range (fun i => algebraMap S T (z i))) = IsLocalRing.maximalIdeal T := by
    rw [Blowups.Etale.LocalCoordinates.Construction.etale_local_maximalIdeal_eq_span_coordinates x q]
    apply congrArg (fun f : σ → T => Ideal.span (Set.range f))
    funext i
    exact (IsScalarTower.algebraMap_apply (MvPolynomial σ K) S T
      (MvPolynomial.X i - MvPolynomial.C (x i))).symm
  have hq : (IsLocalRing.maximalIdeal T).comap (algebraMap S T) = q :=
    Localization.AtPrime.under_maximalIdeal (I := q)
  apply hp2
  rw [← hM]
  apply mapped_coordinate_mem_square_of_derivatives z D
    (Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation_centered x) p
  · rw [hM]
    exact (show p ∈ (IsLocalRing.maximalIdeal T).comap (algebraMap S T) from hq.symm ▸ hp)
  · intro i
    rw [hM]
    exact (show D i p ∈ (IsLocalRing.maximalIdeal T).comap (algebraMap S T) from hq.symm ▸ h i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.TangentCriterion.Construction
