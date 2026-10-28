import OAI.AlgebraicGeometry.DivisorClass.Chern.First
import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedAnalyticFrames

/-! # Iso -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the first Chern class is invariant under actual line-bundle isomorphisms

An isomorphism of the module sheaves produces regular mixed transition units.
Their analytic evaluations give the gauge equivalence on the common cover.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L M : Line.Bundles.AlgebraicLineBundle X) (e : L.sheaf ≅ M.sheaf)

include e in
/-- On a shared analytic cover, an actual module-sheaf isomorphism identifies the classes. -/
theorem Line.Bundles.AlgebraicLineBundle.logarithmicClass_iso_on_cover {I : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (r s : I → X.carrier) (hr : ∀ i, U i ≤ L.analyticCover (r i))
    (hs : ∀ i, U i ≤ M.analyticCover (s i))
    (l l' : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (h' : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = L.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a p) = M.pointTransition (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l' h' =
      LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l h := by
  let g (i : I) : C(U i, ℂ) :=
    (L.mixedTransitionPair M e (r i) (s i)).comp
      (LogRefinementOpen.Construction.openInclusionMap (le_inf (hr i) (hs i)))
  have hg : ∀ i x, g i x ≠ 0 := fun i x => L.mixedTransitionPair_ne_zero M e (r i) (s i) _
  apply ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U g hg hU l l' h h'
  intro a p
  rw [he, he']
  exact L.mixedPointTransition_gauge M e (r (a 0)) (r (a 1)) (s (a 0)) (s (a 1)) p.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))

omit M e in
theorem Line.Bundles.AlgebraicLineBundle.bundleLogCech_exp_point (a : Fin 2 → L.LogCoverIndex)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) :
    Complex.exp (L.bundleLogCech a p) =
      L.pointTransition (L.logParent (a 0)) (L.logParent (a 1)) p.val
        (L.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a 0 p.property))
        (L.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a 1 p.property)) :=
  (L.exp_bundleLogCech a p).trans
    (L.pointTransition_eq_value (L.logParent ∘ a) 0 1
      ⟨p.val, L.logIntersection_subset a p.property⟩).symm

end

/-- The constructed rational first Chern class depends only on the isomorphism
class of the actual algebraic module sheaf. -/
theorem Iso.firstChernClassQ_iso (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L M : Line.Bundles.AlgebraicLineBundle X) (e : L.sheaf ≅ M.sheaf) :
    First.firstChernClassQ X M = First.firstChernClassQ X L := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let W : L.LogCoverIndex × M.LogCoverIndex → Opens T := fun a => L.logCover a.1 ⊓ M.logCover a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := L.logCover_covers x
    obtain ⟨j, hj⟩ := M.logCover_covers x
    exact ⟨(i, j), hi, hj⟩
  have hWL : ∀ a, W a ≤ L.logCover a.1 := fun _ => inf_le_left
  have hWM : ∀ a, W a ≤ M.logCover a.2 := fun _ => inf_le_right
  let k := LogRefinement.RationalCech.refineLogCech T L.logCover W Prod.fst hWL L.bundleLogCech
  let k' := LogRefinement.RationalCech.refineLogCech T M.logCover W Prod.snd hWM M.bundleLogCech
  have hk := LogRefinement.RationalCech.exponentialCocycle_refinement T L.logCover W Prod.fst hWL
    L.bundleLogCech L.bundleLogCech_cocycle
  have hk' := LogRefinement.RationalCech.exponentialCocycle_refinement T M.logCover W Prod.snd hWM
    M.bundleLogCech M.bundleLogCech_cocycle
  have hc : LogCech.RationalCech.logarithmicSingularClass T W hW k' hk' = LogCech.RationalCech.logarithmicSingularClass T W hW k hk := by
    apply L.logarithmicClass_iso_on_cover M e W hW
      (L.logParent ∘ Prod.fst) (M.logParent ∘ Prod.snd)
      (fun a => (hWL a).trans (L.logCover_subset a.1))
      (fun a => (hWM a).trans (M.logCover_subset a.2)) k k' hk hk'
    · intro a p
      exact L.bundleLogCech_exp_point (Prod.fst ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le L.logCover W Prod.fst hWL a p.property⟩
    · intro a p
      exact M.bundleLogCech_exp_point (Prod.snd ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le M.logCover W Prod.snd hWM a p.property⟩
  exact (LogRefinement.RationalCech.logarithmicSingularClass_refinement T M.logCover W Prod.snd hWM
    M.logCover_covers hW M.bundleLogCech M.bundleLogCech_cocycle).symm.trans
    (hc.trans (LogRefinement.RationalCech.logarithmicSingularClass_refinement T L.logCover W Prod.fst hWL
      L.logCover_covers hW L.bundleLogCech L.bundleLogCech_cocycle))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
