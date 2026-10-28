import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierChowIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe

/-! # Isomorphic Divisor Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorDegree.BundleCycles

noncomputable section

section

/-! The actual ideal of a Cartier section has fiber degree minus
one: its fundamental-class intersection pushes to minus the base class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem closedSection_residueDegree {E X : Scheme.{0}} (p : E ⟶ X)
    (s : X ⟶ E) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X) (x : X) :
    p.residueDegree (s x) = 1 := by
  have h := congrArg (fun f : X ⟶ X => f.residueDegree x) hs
  simpa only [IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp, IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion,
    Scheme.Hom.residueDegree_id, one_mul, mul_one] using h

variable {E X : Scheme.{0}} [IsIntegral E] [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p]
    (s : X ⟶ E) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (hCartier : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include hs in
theorem cartierSection_chowIntersection_pushforward (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (p ≫ f) = d + 1) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle s hCartier) (p ≫ f) d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + 1) (Finsupp.single (genericPoint E) 1))) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single (genericPoint X) 1) := by
  rw [LineBundle.GenericClass.Cycles.separatedLineBundleChowIntersection_generic E _ (p ≫ f) d hd,
    Integral.CartierChowIntersection.BundleCycles.integralCartierIdeal_chowClass s hCartier (p ≫ f) d hd,
    map_neg, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single,
    closedSection_residueDegree p s hs, Nat.cast_one, mul_one]
  have h : p (s (genericPoint X)) = genericPoint X := congrArg (fun g : X ⟶ X => g (genericPoint X)) hs
  rw [h]

end

/-! A Cartier divisor that projects isomorphically onto the base
has actual ideal-intersection degree minus one. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem closedIsomorphicDivisor_residueDegree {E X Z : Scheme.{0}}
    (p : E ⟶ X) (i : Z ⟶ E) [IsClosedImmersion i] [IsIso (i ≫ p)] (z : Z) :
    p.residueDegree (i z) = 1 := by
  have h := IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp i p z
  simpa only [IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion, one_mul, mul_one] using h.symm

variable {E X Z : Scheme.{0}} [IsIntegral E] [IsIntegral X] [IsIntegral Z]
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p]
    (i : Z ⟶ E) [IsClosedImmersion i] [IsIso (i ≫ p)]
    (hi : IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem cartierIsomorphicDivisor_chowIntersection_pushforward (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (p ≫ f) = d + 1) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle i hi) (p ≫ f) d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + 1) (Finsupp.single (genericPoint E) 1))) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single (genericPoint X) 1) := by
  rw [LineBundle.GenericClass.Cycles.separatedLineBundleChowIntersection_generic E _ (p ≫ f) d hd,
    Integral.CartierChowIntersection.BundleCycles.integralCartierIdeal_chowClass i hi (p ≫ f) d hd,
    map_neg, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single,
    closedIsomorphicDivisor_residueDegree p i, Nat.cast_one, mul_one]
  have h : p (i (genericPoint Z)) = genericPoint X := genericPoint_eq_of_isOpenImmersion (i ≫ p)
  rw [h]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorDegree.BundleCycles
