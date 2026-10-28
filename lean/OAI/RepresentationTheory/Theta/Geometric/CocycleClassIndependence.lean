import OAI.RepresentationTheory.Theta.Geometric.CocyclePointValues
import OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge

/-! # Cocycle Class Independence -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The singular class of an actual continuous transition cocycle is
independent of its logarithmic cover and the retained parent charts. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge.RationalCech

variable {T : TopCat} {K : Type} (C : ContinuousLine.ContinuousLineCocycle T K)

/-- On one analytic cover, changing the chosen algebraic parent charts
preserves the class of logarithms of the actual transitions. -/
theorem ContinuousLine.ContinuousLineCocycle.logarithmicClass_parent_independent {I : Type}
    (U : I → Opens T) (hU : ∀ x, ∃ i, x ∈ U i)
    (r s : I → K) (hr : ∀ i, U i ≤ C.cover (r i))
    (hs : ∀ i, U i ≤ C.cover (s i))
    (l l' : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T U)
    (h : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle T U l)
    (h' : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle T U l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = C.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a p) = C.pointTransition (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T U hU l' h' =
      AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T U hU l h := by
  let g (i : I) : C(U i, ℂ) :=
    (C.transitionPair (r i) (s i)).comp (AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (le_inf (hr i) (hs i)))
  have hg : ∀ i x, g i x ≠ 0 := fun i x => C.transitionPair_nonzero (r i) (s i) _
  apply AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge
    T U g hg hU l l' h h'
  intro a p
  rw [he, he']
  exact C.pointTransition_gauge (r (a 0)) (r (a 1)) (s (a 0)) (s (a 1)) p.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))

/-- Arbitrary logarithmic covers subordinate to the algebraic trivializing
cover yield the same actual rational singular class. -/
theorem ContinuousLine.ContinuousLineCocycle.logarithmicClass_cover_independent {I J : Type}
    (U : I → Opens T) (hU : ∀ x, ∃ i, x ∈ U i)
    (V : J → Opens T) (hV : ∀ x, ∃ j, x ∈ V j)
    (r : I → K) (s : J → K)
    (hr : ∀ i, U i ≤ C.cover (r i)) (hs : ∀ j, V j ≤ C.cover (s j))
    (l : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T U)
    (l' : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T V)
    (h : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle T U l)
    (h' : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle T V l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = C.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → J) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l' a p) = C.pointTransition (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1 p.property))) :
    AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T V hV l' h' =
      AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T U hU l h := by
  let W : I × J → Opens T := fun a => U a.1 ⊓ V a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := hV x
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWV : ∀ a, W a ≤ V a.2 := fun _ => inf_le_right
  let k := AlgebraicGeometry.DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech T U W Prod.fst hWU l
  let k' := AlgebraicGeometry.DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech T V W Prod.snd hWV l'
  have hk := AlgebraicGeometry.DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement T U W Prod.fst hWU l h
  have hk' := AlgebraicGeometry.DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement T V W Prod.snd hWV l' h'
  have hc : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T W hW k' hk' = AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T W hW k hk := by
    apply C.logarithmicClass_parent_independent W hW (r ∘ Prod.fst) (s ∘ Prod.snd)
      (fun a => (hWU a).trans (hr a.1)) (fun a => (hWV a).trans (hs a.2))
      k k' hk hk'
    · intro a p
      exact he (Prod.fst ∘ a)
        ⟨p.val, AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech.cechIntersection_refinement_le U W Prod.fst hWU a p.property⟩
    · intro a p
      exact he' (Prod.snd ∘ a)
        ⟨p.val, AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech.cechIntersection_refinement_le V W Prod.snd hWV a p.property⟩
  exact (AlgebraicGeometry.DivisorClass.Chern.LogRefinement.RationalCech.logarithmicSingularClass_refinement T V W Prod.snd hWV hV hW l' h').symm.trans
    (hc.trans (AlgebraicGeometry.DivisorClass.Chern.LogRefinement.RationalCech.logarithmicSingularClass_refinement T U W Prod.fst hWU hU hW l h))

variable [CompactSpace T] [NormalSpace T]

theorem ContinuousLine.ContinuousLineCocycle.chernClass_eq_on_cover {J : Type}
    (V : J → Opens T) (hV : ∀ x, ∃ j, x ∈ V j)
    (r : J → K) (hr : ∀ j, V j ≤ C.cover (r j))
    (l : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T V) (hl : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle T V l)
    (he : ∀ (a : Fin 2 → J) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l a p) = C.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1 p.property))) :
    AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T V hV l hl = C.chernClass := by
  apply C.logarithmicClass_cover_independent C.logCover C.logCover_covers V hV
    C.logParent r C.logCover_subset hr C.logarithm l C.logarithm_cocycle hl _ he
  intro a p
  exact (C.exp_logarithm a p).trans (C.transition_eq_point (C.logParent ∘ a)
    ⟨p.val, C.logIntersection_subset a p.property⟩)

end

end OAI.RepresentationTheory.Theta.Geometric
