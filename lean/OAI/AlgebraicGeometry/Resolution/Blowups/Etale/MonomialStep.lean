import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart

/-! # Monomial Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialStep.Construction

noncomputable section

/-! Actual monomial controlled transforms remain in étale polynomial coordinates after each step. -/

open _root_.MvPolynomial

universe u

variable {σ R S : Type u} [CommRing R] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ R) S] [Algebra.Etale (MvPolynomial σ R) S]

/-- The corresponding actual denominator chart after extending the selected center. -/
abbrev etaleSubsetCoordinateChart (C : Finset σ) (i : C) :=
  Blowup.Charts.Construction.blowupChart ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))
    ⟨algebraMap (MvPolynomial σ R) S (X i.val),
      Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩

/-- New polynomial coordinates on the actual étale blowup chart. -/
def etaleSubsetCoordinateMap (C : Finset σ) (i : C) :
    MvPolynomial σ R →+* etaleSubsetCoordinateChart (R := R) (S := S) C i :=
  (ChartLift.Construction.blowupChartMap (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (algebraMap (MvPolynomial σ R) S)
    (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)).comp (SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup C i)

/-- The new coordinate map is étale, so this chart is suitable for another
step of the same monomial algorithm. -/
theorem etaleSubsetCoordinateMap_etale (C : Finset σ) (i : C) :
    (etaleSubsetCoordinateMap (R := R) (S := S) C i).Etale := by
  have hg : (SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup (R := R) C i).Etale :=
    RingHom.Etale.of_bijective (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChartEquiv (R := R) C i).symm.bijective
  exact RingHom.Etale.stableUnderComposition
    (SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup (R := R) C i)
    (ChartLift.Construction.blowupChartMap (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (algebraMap (MvPolynomial σ R) S) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i))
    hg (BlowupChart.Construction.blowupChartMap_ringHom_etale (S := S) (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i))

variable [Fintype σ]

omit [Algebra.Etale (MvPolynomial σ R) S] in
/-- A monomial ideal extended to an étale ambient algebra has precisely
the same controlled exponent update on the corresponding actual Rees chart. -/
theorem etaleSubsetCoordinate_controlledIdeal (a : σ → ℕ) (b : ℕ)
    (C : Finset σ) (hb : b ≤ ∑ j ∈ C, a j) (i : C) :
    ControlledTransform.Construction.blowupControlledTransform
      ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))
      ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}).map (algebraMap (MvPolynomial σ R) S)) b
      ⟨algebraMap (MvPolynomial σ R) S (X i.val),
        Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩ =
      Ideal.span {etaleSubsetCoordinateMap (R := R) (S := S) C i
        (MonomialBlowupChart.Construction.coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b C i.val))} := by
  let I := SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C
  let e : I := SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i
  let J : Ideal (MvPolynomial σ R) := Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}
  have hJ : J ≤ I ^ b := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_le_pow_right hb (SubsetMonomialTransform.Construction.coordinateMonomial_mem_subset_center_power a C)
  have hback := congrArg (fun L => L.map (SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup (R := R) C i))
    (SubsetMonomialTransform.Construction.subsetCoordinateMonomial_controlledIdeal (R := R) a b C hb i)
  rw [Ideal.map_map, SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup_toPolynomial, Ideal.map_id] at hback
  rw [← ControlledTransformMap.Construction.blowupChartMap_controlledIdeal I J e (algebraMap (MvPolynomial σ R) S) b hJ,
    hback, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  rfl

omit [Fintype σ] in
/-- Every minimal-center chart both preserves the étale coordinate setup
and realizes a strict step in the well-founded exponent relation. -/
theorem etaleSubsetCoordinate_minimal_step (a : σ → ℕ) (b : ℕ)
    (C : Finset σ) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) (i : C) :
    (etaleSubsetCoordinateMap (R := R) (S := S) C i).Etale ∧
      MonomialTermination.Construction.MonomialControlledStep b (MonomialTermination.Construction.monomialChartExponents a b C i.val) a :=
  ⟨etaleSubsetCoordinateMap_etale C i, ⟨C, i.val, hC, i.property, rfl⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialStep.Construction
