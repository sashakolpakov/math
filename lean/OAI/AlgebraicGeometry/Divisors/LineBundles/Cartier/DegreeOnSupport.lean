import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChartsPullback

/-! # Degree On Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.DegreeOnSupport.BundleCycles

noncomputable section

/-! The ideal of a Cartier divisor isomorphic to the base has
degree minus one on every integral support of a relative curve. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p 1)
    (s : D ⟶ E) [IsClosedImmersion s] [IsIso (s ≫ p)]
    (hs : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include h in
theorem cartierIsomorphicDivisor_degree_on_support (d : ℕ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + 1) (Finsupp.single (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x) 1))) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x 1) := by
  let W := irreducibleSetEquivPoints.symm x
  let k := CycleClass.Geometric.GenericPoint.reducedSupportι W
  let A := pullback p k
  let a : A ⟶ E := pullback.fst p k
  let q : A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W := pullback.snd p k
  let : AlgebraicGeometry.IsNoetherian A := Integral.PulledSupport.BundleCycles.integralPulledSupportScheme_isNoetherian p W
  let : IsIntegral A := Integral.PulledSupport.BundleCycles.integralPulledSupportScheme_isIntegral p W
  let : A.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).IsSeparated := ⟨by rw [← terminal.comp_from k]; infer_instance⟩
  let j := IsomorphicDivisorBaseChange.BundleCycles.cartierIsomorphicDivisorBaseChangeInclusion p s k
  let B := pullback a s
  let : IsIntegral B := IsIntegral.of_isIso (inv (j ≫ q))
  have hj := IsomorphicDivisorBaseChange.BundleCycles.cartierIsomorphicDivisorBaseChange_regular p s k hs
  have he := IsomorphicDivisorBaseChange.BundleCycles.cartierIsomorphicDivisorBaseChange_idealIso p s k hs
  have hk : k (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = x :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans (irreducibleSetEquivPoints.apply_symm_apply x)
  have ha : a (genericPoint A) = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x := by
    have H := Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality p q k a (IsPullback.of_hasPullback p k).flip
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))
    rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, hk] at H
    exact H
  have hc : a ≫ p = q ≫ k := pullback.condition
  have hf : a ≫ (p ≫ f) = q ≫ (k ≫ f) := by rw [← Category.assoc, hc, Category.assoc]
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (a ≫ (p ≫ f)) = d + 1 := by
    have H := AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension q (k ≫ f) 1 (h.baseChange k)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))
    rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, LineBundle.GenericClass.Cycles.genericPointSupport_dimension, LineBundle.GenericClass.Cycles.genericPointSupport_dimension] at H
    rw [hf, H]
    exact congrArg (fun n => n + 1) hx
  have H := LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowIntersection_proper_projection a (p ≫ f)
    (IdealBundle.Cycles.cartierIdealLineBundle s hs) d
    (Point.CycleChow.BundleCycles.pointCycleToChowQ (a ≫ (p ≫ f)) (d + 1) (Finsupp.single (genericPoint A) 1))
  rw [LineBundle.GenericClass.Cycles.separatedLineBundleChowIntersection_generic A _ _ d hd,
    Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion a,
    Finsupp.mapDomain_single, ha] at H
  have hClass := LineBundle.IsoDivisor.Cycles.lineBundleIso_chowClass he (a ≫ (p ≫ f)) d hd
  have hdj : p.residueDegree (a (j (genericPoint B))) = 1 := by
    have H := congrArg (fun r : A ⟶ X => r.residueDegree (j (genericPoint B))) hc
    simpa only [IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp, IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion, one_mul, mul_one,
      IsomorphicDivisorDegree.BundleCycles.closedIsomorphicDivisor_residueDegree q j] using H
  have hpj : p (a (j (genericPoint B))) = x := by
    have H := congrArg (fun r : A ⟶ X => r (j (genericPoint B))) hc
    have Hq : q (j (genericPoint B)) = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
      genericPoint_eq_of_isOpenImmersion (j ≫ q)
    exact H.trans ((congrArg k Hq).trans hk)
  rw [← H, hClass, Integral.CartierChowIntersection.BundleCycles.integralCartierIdeal_chowClass j hj (a ≫ (p ≫ f)) d hd,
    map_neg, map_neg, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion a, Finsupp.mapDomain_single,
    Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, hdj, Nat.cast_one, mul_one, hpj]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.DegreeOnSupport.BundleCycles
