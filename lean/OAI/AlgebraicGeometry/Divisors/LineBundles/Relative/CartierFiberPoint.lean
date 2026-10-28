import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierChowIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChartsPullback

/-! # Cartier Fiber Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberPoint.BundleCycles

noncomputable section

/-! Intersecting an actual integral fiber support with a relative
Cartier ideal gives minus the corresponding divisor fiber support. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (hs : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))

include h in
theorem relativeCartierIdeal_fiber_point (d : ℕ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d) :
    LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) (d + r)
      (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) ((d + r) + 1) (Finsupp.single (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x) 1)) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + r) (Finsupp.single (s (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (s ≫ p) x)) 1) := by
  let W := irreducibleSetEquivPoints.symm x
  let k := CycleClass.Geometric.GenericPoint.reducedSupportι W
  let A := pullback p k
  let a : A ⟶ E := pullback.fst p k
  let q : A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W := pullback.snd p k
  let : AlgebraicGeometry.IsNoetherian A := Integral.PulledSupport.BundleCycles.integralPulledSupportScheme_isNoetherian p W
  let : IsIntegral A := Integral.PulledSupport.BundleCycles.integralPulledSupportScheme_isIntegral p W
  let : A.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  let B := pullback a s
  let j : B ⟶ A := pullback.fst a s
  let b : B ⟶ D := pullback.snd a s
  have hp : IsPullback (j ≫ q) b k (s ≫ p) :=
    (IsPullback.of_hasPullback a s).paste_horiz (IsPullback.of_hasPullback p k).flip
  let : Smooth (j ≫ q) := MorphismProperty.of_isPullback hp.flip inferInstance
  let : GeometricallyIntegral (j ≫ q) := MorphismProperty.of_isPullback hp.flip inferInstance
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian (j ≫ q)
  let : IsIntegral B := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (j ≫ q)
  have hj := CartierBaseChange.BundleCycles.relativeCartier_regularPrincipalImageIdeals_baseChange p q a k
    (IsPullback.of_hasPullback p k) s j b (IsPullback.of_hasPullback a s) hs
  have he := Cartier.IdealPullbackIso.BundleCycles.cartierIdealPullbackIso s j a b (IsPullback.of_hasPullback a s) hs hj
  have hk : k (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = x :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans (irreducibleSetEquivPoints.apply_symm_apply x)
  have ha : a (genericPoint A) = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x := by
    have H := Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality p q k a (IsPullback.of_hasPullback p k).flip
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))
    rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, hk] at H
    exact H
  have hb : b (genericPoint B) = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (s ≫ p) x := by
    have H := Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality (s ≫ p) (j ≫ q) k b hp
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))
    rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, hk] at H
    exact H
  have hf : a ≫ (p ≫ f) = q ≫ (k ≫ f) := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (a ≫ (p ≫ f)) = (d + r) + 1 := by
    have H := AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension q (k ≫ f) (r + 1) (h.baseChange k)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))
    rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, LineBundle.GenericClass.Cycles.genericPointSupport_dimension, LineBundle.GenericClass.Cycles.genericPointSupport_dimension] at H
    rw [hf, H]
    exact congrArg (fun n => n + (r + 1)) hx
  have H := LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowIntersection_proper_projection a (p ≫ f)
    (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (d + r)
    (Point.CycleChow.BundleCycles.pointCycleToChowQ (a ≫ (p ≫ f)) ((d + r) + 1) (Finsupp.single (genericPoint A) 1))
  rw [LineBundle.GenericClass.Cycles.separatedLineBundleChowIntersection_generic A _ _ (d + r) hd,
    Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion a,
    Finsupp.mapDomain_single, ha] at H
  have hClass := LineBundle.IsoDivisor.Cycles.lineBundleIso_chowClass he (a ≫ (p ≫ f)) (d + r) hd
  have hjb : a (j (genericPoint B)) = s (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (s ≫ p) x) :=
    (congrArg (fun k : B ⟶ E => k (genericPoint B)) (pullback.condition (f := a) (g := s))).trans
      (congrArg s hb)
  rw [← H, hClass, Integral.CartierChowIntersection.BundleCycles.integralCartierIdeal_chowClass j hj (a ≫ (p ≫ f)) (d + r) hd,
    map_neg, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion a,
    Finsupp.mapDomain_single, hjb]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberPoint.BundleCycles
