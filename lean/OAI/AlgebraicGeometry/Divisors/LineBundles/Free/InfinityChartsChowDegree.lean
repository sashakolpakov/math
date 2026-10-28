import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsBaseChangeDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeClosedSquare

/-! # Infinity Charts Chow Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChartsChowDegree.BundleCycles

noncomputable section

section

/-! Actual integral supports reduce the global degree calculation
for each cycle generator to its top-dimensional base-change calculation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include H in
theorem freeInfinityCharts_degree_point (d : ℕ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x 1)))) =
      (-1 : ℚ) ^ r • Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x 1) := by
  let W := irreducibleSetEquivPoints.symm x
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W
  let q := pullback.snd p i
  let j := pullback.fst p i
  let A := Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d (Finsupp.single (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) 1)
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  have hA : Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d A = Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x 1) := by
    have hi : i (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = x :=
      (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans (irreducibleSetEquivPoints.apply_symm_apply x)
    change Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d _) = _
    rw [Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass, Finsupp.mapDomain_single, hi]
  have Htop := ChartsBaseChangeDegree.BundleCycles.freeInfinityCharts_baseChange_top_degree p L H i (i ≫ f) r hp d hx A
  have Hclosed := AffineSource.DegreeClosedSquare.BundleCycles.affineSourceChowDegree_closedSquare p q i j (IsPullback.of_hasPullback p i).flip
    f L r hp (hp.baseChange i) d A
  rw [hA, Htop, map_smul, hA] at Hclosed
  exact Hclosed

end

/-! The actual proper intersection degree is the expected unit
on every Chow class for a bundle with genuine free infinity charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include H in
theorem freeInfinityCharts_chow_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α)) =
      (-1 : ℚ) ^ r • α := by
  let T := (Proper.ChowNe.BundleCycles.properChowPushforward p f d).comp
    ((LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r).comp (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d))
  let S : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d := (-1 : ℚ) ^ r • LinearMap.id
  have hOne (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) :
      T (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x 1)) = S (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x 1)) := by
    rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d (Finsupp.single x 1)]
    rw [show Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Finsupp.single x 1) = Finsupp.single x.val 1 from
      Finsupp.mapDomain_single]
    exact freeInfinityCharts_degree_point p L H f r hp d x.val x.property
  have hT : T.comp (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) = S.comp (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) := by
    apply Finsupp.lhom_ext
    intro x a
    change T (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x a)) = S (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x a))
    rw [show Finsupp.single x a = a • Finsupp.single x (1 : ℚ) by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul, map_smul, hOne]
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  exact LinearMap.congr_fun hT z

include H L in
theorem affineSpaceSourceChowExtension_injective_of_freeInfinityCharts (d : ℕ) :
    Function.Injective (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d) := by
  intro α β h
  apply sub_eq_zero.mp
  have hz : AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d (α - β) = 0 := by rw [map_sub, h, sub_self]
  have hd := freeInfinityCharts_chow_degree p L H f r hp d (α - β)
  rw [hz, map_zero, map_zero] at hd
  exact (smul_eq_zero.mp hd.symm).resolve_left (pow_ne_zero r (by norm_num))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChartsChowDegree.BundleCycles
