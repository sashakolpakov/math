import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.DescentCohomology
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.DescentRefinement

/-! # Integral Sheaf Lattice -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralSheafLattice

noncomputable section

section

/-! Actual integral scaling for degree-two rational singular and sheaf cohomology. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) [CompactSpace X] [MetrizableSpace X]
  [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

theorem exists_integralSheafMultiple_of_singular
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    ∃ N : ℕ, 0 < N ∧ ∃ b : CategoryTheory.Sheaf.H (IntegralConstantSheaf.integralConstantSheaf X) 2,
      CategoryTheory.Sheaf.H.map (Rational.HolomorphicPeriod.integralToRationalConstantSheaf X) 2 b =
        N • Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1 a := by
  let : MetricSpace X := metrizableSpaceMetric X
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X 2 a
  obtain ⟨I, U, hU, ⟨d⟩⟩ := Singular.CechDescent.exists_singularCechDescentData c
  obtain ⟨k, hk⟩ := d.exists_cechCocycle
  obtain ⟨r, N, hN, g, hg, he⟩ := Cech.IntegralRefinement.exists_integral_cech_refinement U hU 2 k.val
    (Intrinsic.DescentCohomology.rationalCechCocycle_closed U 1 k)
  let dr := d.refine r.cover Subtype.val r.subset
  let ds := dr.nsmul N
  let ki := IntegralCechRepresentative.integerCechRationalCocycle r.cover 2 g hg
  have heN : ki.val = N • Rational.Cech.RationalCech.cechRefinementMap (Cech.Obj.RationalCech.locallyConstantPresheaf X)
      U r.cover Subtype.val r.subset 2 k.val := by
    change Cech.IntegralRefinement.integerCechRationalize r.cover 2 g = _
    rw [he, Nat.cast_smul_eq_nsmul]
  have hki : Cech.Obj.RationalCech.locallyConstantCechEvaluation X r.cover 2 ki.val =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) r.cover 1 ds.horizontal := by
    rw [heN]
    exact dr.nsmul_cocycle N _ (d.refine_cocycle r.cover Subtype.val r.subset k.val hk)
  have hcover : ⨆ i, r.cover i = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨i, hi⟩ := r.covers x
    exact (le_iSup r.cover i) hi
  refine ⟨N, hN, IntegralCechSheaf.integerCechSheafClass r.cover hcover 1 g hg, ?_⟩
  rw [IntegralCechSheaf.integerCechSheafClass_rationalize]
  change Abelian.CechComparison.abelianCechToSheaf r.cover (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) hcover 1
      (Intrinsic.DescentCohomology.rationalNativeCechClass r.cover 1 ki) = _
  rw [ds.native_sheaf_class ki hki hcover]
  change Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1 (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 2 (N • c)) = _
  rw [map_nsmul, map_nsmul]

theorem exists_integralSheafMultiple
    (a : CategoryTheory.Sheaf.H (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) 2) :
    ∃ N : ℕ, 0 < N ∧ ∃ b : CategoryTheory.Sheaf.H (IntegralConstantSheaf.integralConstantSheaf X) 2,
      CategoryTheory.Sheaf.H.map (Rational.HolomorphicPeriod.integralToRationalConstantSheaf X) 2 b = N • a := by
  obtain ⟨c, rfl⟩ := (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1).surjective a
  exact exists_integralSheafMultiple_of_singular X c

end

/-! Rational classes with zero holomorphic obstruction lift through the actual exponential sequence after scaling. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [MetrizableSpace M]
  [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

theorem exists_holomorphicUnitClass_rational_multiple
    (a : Rational.HolomorphicPeriod.rationalSheafCohomologyTwo M) (ha : Rational.HolomorphicPeriod.rationalHolomorphicObstruction E M a = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Holomorphic.Connecting.holomorphicUnitCohomology E M,
      Rational.HolomorphicPeriod.integralToRationalSheafCohomology M (Holomorphic.Connecting.holomorphicExponentialConnecting E M u) = N • a := by
  obtain ⟨N, hN, b, hb⟩ := exists_integralSheafMultiple (TopCat.of M) a
  have hp : Holomorphic.Connecting.holomorphicPeriodCohomologyMap E M b = 0 := by
    rw [Rational.HolomorphicPeriod.holomorphicPeriodCohomologyMap_factor]
    change Rational.HolomorphicPeriod.rationalHolomorphicObstruction E M
      (CategoryTheory.Sheaf.H.map (Rational.HolomorphicPeriod.integralToRationalConstantSheaf (TopCat.of M)) 2 b) = 0
    rw [hb, map_nsmul, ha, smul_zero]
  obtain ⟨u, hu⟩ := Holomorphic.Connecting.exists_holomorphicUnitCohomology_of_period_zero E M b hp
  refine ⟨N, hN, u, ?_⟩
  rw [hu]
  exact hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralSheafLattice
