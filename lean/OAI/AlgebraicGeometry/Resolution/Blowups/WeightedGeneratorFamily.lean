import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledGeneratorFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedHypersurfaceTransform

/-! # Weighted Generator Family -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily.Construction

noncomputable section

/-! A fixed-family weighted coefficient ideal with exact compatibility under repeated transforms. -/

section

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The weighted coefficient ideal of a fixed generating family. -/
def weightedCoordinateDerivativeFamilyIdeal (D : Derivation k A A) (z : A) (p : ι → A) (b : ℕ) :
    Ideal (A ⧸ Ideal.span {z}) :=
  WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val)

variable {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ]

include σ K in
/-- The fixed family detects precisely the order of its generated ideal at
every closed point of a coordinate hypersurface. -/
theorem closedPoint_span_order_iff_weighted_family [Algebra ℚ A]
    (D : Derivation k A A) (z : A) (hz : D z = 1)
    [Algebra (MvPolynomial σ K) (A ⧸ Ideal.span {z})]
    [Algebra.Etale (MvPolynomial σ K) (A ⧸ Ideal.span {z})]
    (p : ι → A) (M : Ideal A) [M.IsMaximal] (hzM : z ∈ M) (b : ℕ) :
    Ideal.span (Set.range p) ≤ M ^ b ↔ weightedCoordinateDerivativeFamilyIdeal D z p b ≤
      M.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  let N := M.map (Ideal.Quotient.mk (Ideal.span {z}))
  let : N.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact (Ideal.span_singleton_le_iff_mem M).mpr hzM)
  rw [HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hz p M hzM b]
  change (∀ j < b, HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j ≤ N ^ (b - j)) ↔
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val) ≤ N ^ b.factorial
  rw [ClosedWeightedOrder.Construction.etale_closedPoint_weighted_order_iff (σ := σ) (K := K) N]
  exact ⟨fun h j => h j.val j.isLt, fun h j hj => h ⟨j, hj⟩⟩

end

variable {R ι : Type*} [CommRing R] [IsNoetherianRing R] [Algebra ℚ R]

/-- Transforming the weighted ideal of a fixed family gives exactly the
weighted ideal of that family's actual divided generators. The index set is
unchanged, so the same equality applies at each subsequent permissible step. -/
theorem weightedCoordinateDerivativeFamilyIdeal_blowup_colon
    (I : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) (p : ι → R) (b : ℕ)
    (hp : Ideal.span (Set.range p) ≤ I ^ b) :
    ((weightedCoordinateDerivativeFamilyIdeal D z.val p b).map
      (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
        (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
          (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ b.factorial}) =
      weightedCoordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D)
        (ExceptionalIdeal.Construction.blowupChartRatio I a z) (ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p a b hp) b := by
  let c := Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) (Blowup.Charts.Construction.blowupChartConstants I a a.val)
  unfold weightedCoordinateDerivativeFamilyIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  rw [WeightedCoefficientTransform.Construction.weightedCoefficientIdeal_factorization c b _
    (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D)
      (ExceptionalIdeal.Construction.blowupChartRatio I a z) (ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p a b hp) j.val)
    (fun j => ControlledGeneratorFamily.Construction.coordinateDerivativeFamilyIdeal_blowup_factorization I a z D ha p _ b j.val
      (Nat.le_of_lt j.isLt) (ControlledGeneratorFamily.Construction.blowupChartTransformFamily_spec I p a b hp))]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _
    ((NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular I a z D ha hz).pow b.factorial)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily.Construction
