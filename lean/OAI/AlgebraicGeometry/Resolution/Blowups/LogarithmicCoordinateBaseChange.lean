import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinateGenerators
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativePartialBaseChange

/-! # Logarithmic Coordinate Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinateBaseChange.Construction

noncomputable section

/-! Exact étale compatibility of logarithmic differential ideals in boundary coordinates. -/

variable {σ k R S : Type*} [Field k] [CommRing R] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]
  [Algebra R S] [Algebra.FormallyEtale R S]
  [Algebra (MvPolynomial σ k) S] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k S] [IsScalarTower k R S] [IsScalarTower k (MvPolynomial σ k) S]
  [IsScalarTower (MvPolynomial σ k) R S]

theorem etaleLogarithmicPartial_baseChange (B : Finset σ) (i : σ) (x : R) :
    LogarithmicCoordinateGenerators.Construction.etaleLogarithmicPartial (k := k) (R := S) B i (algebraMap R S x) =
      algebraMap R S (LogarithmicCoordinateGenerators.Construction.etaleLogarithmicPartial (k := k) B i x) := by
  simp only [LogarithmicCoordinateGenerators.Construction.etaleLogarithmicPartial, Derivation.smul_apply, smul_eq_mul, map_mul,
    Blowups.Etale.RelativePartialBaseChange.Construction.etaleRelativePartial_baseChange (S := R) (T := S)]
  by_cases hi : i ∈ B
  · simp only [ite_eq_left hi]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) R S]
  · simp only [ite_eq_right hi, map_one]

variable [Fintype σ]

theorem firstRelativeLogarithmicDifferentialIdeal_coordinate_baseChange
    (B : Finset σ) (J : Ideal R) :
    (Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k
      (fun j : B => algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) J).map (algebraMap R S) =
      Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k
        (fun j : B => algebraMap (MvPolynomial σ k) S (MvPolynomial.X j.val)) (J.map (algebraMap R S)) := by
  let w (j : B) := algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)
  let L := (Relative.LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J).map (algebraMap R S)
  have hw : (fun j : B => algebraMap R S (w j)) =
      (fun j : B => algebraMap (MvPolynomial σ k) S (MvPolynomial.X j.val)) := by
    funext j
    exact (IsScalarTower.algebraMap_apply (MvPolynomial σ k) R S (MvPolynomial.X j.val)).symm
  apply le_antisymm
  · have h := Relative.LogarithmicBoundary.Construction.firstRelativeLogarithmicDifferentialIdeal_map_le (S := S) k w J
    rw [hw] at h
    exact h
  · rw [LogarithmicCoordinateGenerators.Construction.firstRelativeLogarithmicDifferentialIdeal_coordinate_generators]
    have hJ : J.map (algebraMap R S) ≤ L := Ideal.map_mono (Relative.LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k w J)
    apply sup_le hJ
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, x⟩, rfl⟩
    let p (y : J) := algebraMap R S y.val
    have hspan : Ideal.span (Set.range p) = J.map (algebraMap R S) := by
      have hs : Ideal.span (Set.range (Subtype.val : J → R)) = J := by
        rw [Subtype.range_val, Ideal.span_eq]
      have hm := congrArg (Ideal.map (algebraMap R S)) hs
      rw [Ideal.map_span, ← Set.range_comp] at hm
      exact hm
    have hx : x.val ∈ Ideal.span (Set.range p) := hspan.symm ▸ x.property
    have hD := Relative.DifferentialBlowup.Construction.relative_derivation_of_span k (LogarithmicCoordinateGenerators.Construction.etaleLogarithmicPartial (k := k) (R := S) B i) p hx
    apply (sup_le (hspan.le.trans hJ) ?_) hD
    apply Ideal.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change LogarithmicCoordinateGenerators.Construction.etaleLogarithmicPartial (k := k) (R := S) B i (algebraMap R S y.val) ∈ L
    rw [etaleLogarithmicPartial_baseChange]
    exact Ideal.mem_map_of_mem _ (Relative.LogarithmicIdeal.Construction.relative_logarithmic_derivation_mem_first k w J
      ⟨_, LogarithmicCoordinateGenerators.Construction.etaleLogarithmicPartial_logarithmic B i⟩ y.property)

theorem iteratedRelativeLogarithmicDifferentialIdeal_coordinate_baseChange
    (B : Finset σ) (J : Ideal R) (n : ℕ) :
    (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
      (fun j : B => algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) J n).map (algebraMap R S) =
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
        (fun j : B => algebraMap (MvPolynomial σ k) S (MvPolynomial.X j.val)) (J.map (algebraMap R S)) n := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
      simp only [Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal]
      rw [ih, firstRelativeLogarithmicDifferentialIdeal_coordinate_baseChange]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinateBaseChange.Construction
