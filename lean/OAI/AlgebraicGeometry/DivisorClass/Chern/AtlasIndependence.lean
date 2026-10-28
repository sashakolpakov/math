import OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms
import OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge

/-! # Atlas Independence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: independence from logarithmic covers and their algebraic parent charts

Two covers carrying logarithms of the actual line-bundle transitions can be
compared on their intersection cover. The change between their parent charts
is an actual nowhere-zero algebraic transition function. Its proved gauge
identity and continuous gauge invariance identify the resulting classes.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- On one analytic cover, changing the chosen algebraic parent charts
preserves the class of logarithms of the actual transitions. -/
theorem Line.Bundles.AlgebraicLineBundle.logarithmicClass_parent_independent {I : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (r s : I → X.carrier) (hr : ∀ i, U i ≤ L.analyticCover (r i))
    (hs : ∀ i, U i ≤ L.analyticCover (s i))
    (l l' : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (h' : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = L.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a p) = L.pointTransition (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l' h' =
      LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l h := by
  let g (i : I) : C(U i, ℂ) :=
    (L.transitionPair (r i) (s i)).comp (LogRefinementOpen.Construction.openInclusionMap (le_inf (hr i) (hs i)))
  have hg : ∀ i x, g i x ≠ 0 := fun i x => L.transitionPair_ne_zero (r i) (s i) _
  apply ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U g hg hU l l' h h'
  intro a p
  rw [he, he']
  exact L.pointTransition_gauge (r (a 0)) (r (a 1)) (s (a 0)) (s (a 1)) p.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))

/-- Arbitrary logarithmic covers subordinate to the algebraic trivializing
cover yield the same actual rational singular class. -/
theorem Line.Bundles.AlgebraicLineBundle.logarithmicClass_cover_independent {I J : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (V : J → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hV : ∀ x, ∃ j, x ∈ V j)
    (r : I → X.carrier) (s : J → X.carrier)
    (hr : ∀ i, U i ≤ L.analyticCover (r i)) (hs : ∀ j, V j ≤ L.analyticCover (s j))
    (l : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (l' : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (h' : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = L.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → J) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l' a p) = L.pointTransition (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1 p.property))) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V hV l' h' =
      LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l h := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let W : I × J → Opens T := fun a => U a.1 ⊓ V a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := hV x
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWV : ∀ a, W a ≤ V a.2 := fun _ => inf_le_right
  let k := LogRefinement.RationalCech.refineLogCech T U W Prod.fst hWU l
  let k' := LogRefinement.RationalCech.refineLogCech T V W Prod.snd hWV l'
  have hk := LogRefinement.RationalCech.exponentialCocycle_refinement T U W Prod.fst hWU l h
  have hk' := LogRefinement.RationalCech.exponentialCocycle_refinement T V W Prod.snd hWV l' h'
  have hc : LogCech.RationalCech.logarithmicSingularClass T W hW k' hk' = LogCech.RationalCech.logarithmicSingularClass T W hW k hk := by
    apply L.logarithmicClass_parent_independent W hW (r ∘ Prod.fst) (s ∘ Prod.snd)
      (fun a => (hWU a).trans (hr a.1)) (fun a => (hWV a).trans (hs a.2))
      k k' hk hk'
    · intro a p
      exact he (Prod.fst ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U W Prod.fst hWU a p.property⟩
    · intro a p
      exact he' (Prod.snd ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le V W Prod.snd hWV a p.property⟩
  exact (LogRefinement.RationalCech.logarithmicSingularClass_refinement T V W Prod.snd hWV hV hW l' h').symm.trans
    (hc.trans (LogRefinement.RationalCech.logarithmicSingularClass_refinement T U W Prod.fst hWU hU hW l h))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
