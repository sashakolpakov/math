import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions

/-! # Chern Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison

noncomputable section

section

/-! Logarithms taken in arbitrary actual sheaf frames compute the same
rational singular class. Frame gauges and a common cover prove this,
without synchronizing any chosen trivializing atlas. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {M : X.carrier.Modules}

theorem frameLogClass_parent_independent {I : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (r s : I → LineFrameAtlas.LocalLineFrame M)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (r i)) (hs : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (s i))
    (l l' : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (h' : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = AnalyticFrameTransitions.framePointTransition X (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a p) = AnalyticFrameTransitions.framePointTransition X (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l' h' =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l h := by
  let g (i : I) : C(U i, ℂ) :=
    (AnalyticFrameTransitions.frameTransitionPair X (r i) (s i)).comp (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (le_inf (hr i) (hs i)))
  have hg : ∀ i x, g i x ≠ 0 := fun i x => AnalyticFrameTransitions.frameTransitionPair_ne_zero X (r i) (s i) _
  apply DivisorClass.Chern.ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U g hg hU l l' h h'
  intro a p
  rw [he, he']
  exact AnalyticFrameTransitions.framePointTransition_gauge X (r (a 0)) (r (a 1)) (s (a 0)) (s (a 1)) p.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))

theorem frameLogClass_cover_independent {I J : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (V : J → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hV : ∀ x, ∃ j, x ∈ V j)
    (r : I → LineFrameAtlas.LocalLineFrame M) (s : J → LineFrameAtlas.LocalLineFrame M)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (r i)) (hs : ∀ j, V j ≤ AnalyticFrameTransitions.frameAnalyticOpen X (s j))
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (l' : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V)
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (h' : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V l')
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = AnalyticFrameTransitions.framePointTransition X (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → J) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l' a p) = AnalyticFrameTransitions.framePointTransition X (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1 p.property))) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V hV l' h' =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l h := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let W : I × J → Opens T := fun a => U a.1 ⊓ V a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := hV x
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWV : ∀ a, W a ≤ V a.2 := fun _ => inf_le_right
  let k := DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech T U W Prod.fst hWU l
  let k' := DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech T V W Prod.snd hWV l'
  have hk := DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement T U W Prod.fst hWU l h
  have hk' := DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement T V W Prod.snd hWV l' h'
  have hc : DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T W hW k' hk' = DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass T W hW k hk := by
    apply frameLogClass_parent_independent X W hW (r ∘ Prod.fst) (s ∘ Prod.snd)
      (fun a => (hWU a).trans (hr a.1)) (fun a => (hWV a).trans (hs a.2)) k k' hk hk'
    · intro a p
      exact he (Prod.fst ∘ a) ⟨p.val, DivisorClass.Chern.Rational.Cech.RationalCech.cechIntersection_refinement_le U W Prod.fst hWU a p.property⟩
    · intro a p
      exact he' (Prod.snd ∘ a) ⟨p.val, DivisorClass.Chern.Rational.Cech.RationalCech.cechIntersection_refinement_le V W Prod.snd hWV a p.property⟩
  exact (DivisorClass.Chern.LogRefinement.RationalCech.logarithmicSingularClass_refinement T V W Prod.snd hWV hV hW l' h').symm.trans
    (hc.trans (DivisorClass.Chern.LogRefinement.RationalCech.logarithmicSingularClass_refinement T U W Prod.fst hWU hU hW l h))

end

/-! Arbitrary genuine local sheaf frames compute ChernClass's original native
first Chern class. The comparison is proved by inserting its chosen
frames into the full frame atlas and using the actual transition units. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem frameLog_exponentialCocycle {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {M : X.carrier.Modules} {I : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (r : I → LineFrameAtlas.LocalLineFrame M)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (r i))
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = AnalyticFrameTransitions.framePointTransition X (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l := by
  intro a p
  change Complex.exp (l (a ∘ (2 : Fin 3).succAbove) _) *
    Complex.exp (l (a ∘ (0 : Fin 3).succAbove) _) = Complex.exp (l (a ∘ (1 : Fin 3).succAbove) _)
  rw [he, he, he]
  exact AnalyticFrameTransitions.framePointTransition_cocycle X (r (a 0)) (r (a 1)) (r (a 2)) p.val _ _ _

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X)

def chosenLineFrame (i : X.carrier) : LineFrameAtlas.LocalLineFrame L.sheaf where
  domain := L.trivializingOpen i
  frame := L.trivialization i

theorem chosenLineFrame_transition (i j : X.carrier) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hi : p ∈ L.analyticCover i) (hj : p ∈ L.analyticCover j) :
    AnalyticFrameTransitions.framePointTransition X (chosenLineFrame L i) (chosenLineFrame L j) p hi hj =
      L.pointTransition i j p hi hj := by
  let U := L.trivializingOpen i ⊓ L.trivializingOpen j
  let q : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U := ⟨p, hi, hj⟩
  exact (AnalyticFrameTransitions.framePointTransition_restrict X (chosenLineFrame L i) (chosenLineFrame L j) U
    inf_le_left inf_le_right q).trans (L.pointTransition_restrict i j U inf_le_left inf_le_right q).symm

/-- Logarithms in any actual local frames compute the original native
first Chern class, without an assumed comparison between the atlases. -/
theorem firstChernClass_eq_frameLogs {I : Type}
    (U : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (r : I → LineFrameAtlas.LocalLineFrame L.sheaf) (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (r i))
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = AnalyticFrameTransitions.framePointTransition X (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    DivisorClass.Chern.First.firstChernClassQ X L =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U hU l h := by
  apply frameLogClass_cover_independent X U hU L.logCover L.logCover_covers r
    (fun i => chosenLineFrame L (L.logParent i)) hr L.logCover_subset l L.bundleLogCech h
    L.bundleLogCech_cocycle he
  intro a p
  exact (L.bundleLogCech_exp_point a p).trans
    (chosenLineFrame_transition L (L.logParent (a 0)) (L.logParent (a 1)) p.val
      (L.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a 0 p.property))
      (L.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a 1 p.property))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison
