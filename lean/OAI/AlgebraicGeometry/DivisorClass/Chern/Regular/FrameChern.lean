import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameAnalyticTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.Iso

/-! # Frame Chern -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular

noncomputable section

section

/-! The original rational Chern class is unchanged by explicit regular section frames. -/

open _root_.CategoryTheory _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle P} {ι : Type}
  (A : FrameAnalyticTransitions.RegularSectionFrameAtlas L ι)

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.logarithmicClass_on_cover {κ : Type}
    (U : κ → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (r : κ → P.carrier) (t : κ → ι)
    (hr : ∀ i, U i ≤ L.analyticCover (r i)) (ht : ∀ i, U i ≤ A.analyticDomain (t i))
    (l l' : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U l)
    (h' : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U l')
    (he : ∀ (a : Fin 2 → κ) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = L.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)))
    (he' : ∀ (a : Fin 2 → κ) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a p) = A.pointTransition (t (a 0)) (t (a 1)) p.val
        (ht (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (ht (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U hU l' h' =
      LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U hU l h := by
  let g (i : κ) : C(U i, ℂ) :=
    (A.mixedPair (r i) (t i)).comp (LogRefinementOpen.Construction.openInclusionMap (le_inf (hr i) (ht i)))
  have hg : ∀ i x, g i x ≠ 0 := fun i x => A.mixedPair_ne_zero (r i) (t i) _
  apply ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U g hg hU l l' h h'
  intro a p
  rw [he, he']
  exact A.mixedPointTransition_gauge (r (a 0)) (r (a 1)) (t (a 0)) (t (a 1)) p.val
    (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    (ht (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
    (ht (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))

end

section

/-! The original algebraic first Chern class can be computed with the constructed regular section frames on any subordinate logarithmic cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle P} {ι : Type}
  (A : FrameAnalyticTransitions.RegularSectionFrameAtlas L ι)

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.firstChernClassQ_eq_on_cover {κ : Type}
    (U : κ → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) (hU : ∀ x, ∃ i, x ∈ U i)
    (t : κ → ι) (ht : ∀ i, U i ≤ A.analyticDomain (t i))
    (l : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U l)
    (he : ∀ (a : Fin 2 → κ) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = A.pointTransition (t (a 0)) (t (a 1)) p.val
        (ht (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (ht (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U hU l h =
      First.firstChernClassQ P L := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
  let W : κ × L.LogCoverIndex → Opens T := fun a => U a.1 ⊓ L.logCover a.2
  have hW : ∀ x, ∃ a, x ∈ W a := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨j, hj⟩ := L.logCover_covers x
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWL : ∀ a, W a ≤ L.logCover a.2 := fun _ => inf_le_right
  let k := LogRefinement.RationalCech.refineLogCech T L.logCover W Prod.snd hWL L.bundleLogCech
  let k' := LogRefinement.RationalCech.refineLogCech T U W Prod.fst hWU l
  have hk := LogRefinement.RationalCech.exponentialCocycle_refinement T L.logCover W Prod.snd hWL
    L.bundleLogCech L.bundleLogCech_cocycle
  have hk' := LogRefinement.RationalCech.exponentialCocycle_refinement T U W Prod.fst hWU l h
  have hc : LogCech.RationalCech.logarithmicSingularClass T W hW k' hk' = LogCech.RationalCech.logarithmicSingularClass T W hW k hk := by
    apply A.logarithmicClass_on_cover W hW (L.logParent ∘ Prod.snd) (t ∘ Prod.fst)
      (fun a => (hWL a).trans (L.logCover_subset a.2))
      (fun a => (hWU a).trans (ht a.1)) k k' hk hk'
    · intro a p
      exact L.bundleLogCech_exp_point (Prod.snd ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le L.logCover W Prod.snd hWL a p.property⟩
    · intro a p
      exact he (Prod.fst ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U W Prod.fst hWU a p.property⟩
  exact (LogRefinement.RationalCech.logarithmicSingularClass_refinement T U W Prod.fst hWU hU hW l h).symm.trans
    (hc.trans (LogRefinement.RationalCech.logarithmicSingularClass_refinement T L.logCover W Prod.snd hWL
      L.logCover_covers hW L.bundleLogCech L.bundleLogCech_cocycle))

end

/-! Actual logarithmic refinements of the explicitly constructed regular frame atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle P} {ι : Type}
  (A : FrameAnalyticTransitions.RegularSectionFrameAtlas L ι)

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.analyticDomain_covers (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) : ∃ i, p ∈ A.analyticDomain i := by
  have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ iSup A.domain := by rw [A.covers]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h
  exact ⟨i, hi⟩

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.transitionPair_ne_zero (i j : ι)
    (p : (A.analyticDomain i ⊓ A.analyticDomain j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver))) :
    A.transitionPair i j p ≠ 0 := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero P _ _ _

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.pointTransition_cocycle (i j k : ι) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hi : p ∈ A.analyticDomain i) (hj : p ∈ A.analyticDomain j) (hk : p ∈ A.analyticDomain k) :
    A.pointTransition i j p hi hj * A.pointTransition j k p hj hk = A.pointTransition i k p hi hk := by
  let W := A.domain i ⊓ A.domain j ⊓ A.domain k
  have hWi : W ≤ A.domain i := inf_le_left.trans inf_le_left
  have hWj : W ≤ A.domain j := inf_le_left.trans inf_le_right
  have hWk : W ≤ A.domain k := inf_le_right
  let q : Line.Bundles.AlgebraicLineBundle.analyticOpen P W := ⟨p, ⟨hi, hj⟩, hk⟩
  have h := congrArg (fun t : Γ(P.carrier, W)ˣ => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (t : Γ(P.carrier, W)) q)
    (FramesFrame.Construction.frameTransitionUnit_cocycle (A.frame i W hWi) (A.frame j W hWj) (A.frame k W hWk))
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W ((A.transition i j W hWi hWj : Γ(P.carrier, W)) *
    (A.transition j k W hWj hWk : Γ(P.carrier, W))) q =
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (A.transition i k W hWi hWk : Γ(P.carrier, W)) q at h
  rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, ← A.pointTransition_restrict, ← A.pointTransition_restrict,
    ← A.pointTransition_restrict] at h
  exact h

def FrameAnalyticTransitions.RegularSectionFrameAtlas.logRefinement : LogRefinementOpen.Construction.CompactLogarithmicRefinement A.analyticDomain A.transitionPair :=
  Classical.choice (LogRefinementOpen.Construction.nonempty_compactLogarithmicRefinement A.analyticDomain A.analyticDomain_covers
    A.transitionPair A.transitionPair_ne_zero)

abbrev FrameAnalyticTransitions.RegularSectionFrameAtlas.LogIndex := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver × A.logRefinement.charts
abbrev FrameAnalyticTransitions.RegularSectionFrameAtlas.logCover : A.LogIndex → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) := A.logRefinement.refinement.cover

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.logCover_subset (a : A.LogIndex) : A.logCover a ≤ A.analyticDomain a.2.val :=
  A.logRefinement.refinement.subset a

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.logCover_covers (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) : ∃ a, p ∈ A.logCover a :=
  A.logRefinement.refinement.covers p

def FrameAnalyticTransitions.RegularSectionFrameAtlas.logCech : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) A.logCover :=
  fun a => (A.logRefinement.refinement.logarithm (a 0) (a 1)).comp
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.cechIntersection_le_pair A.logCover a))

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.exp_logCech (a : Fin 2 → A.LogIndex) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.logCover a) :
    Complex.exp (A.logCech a p) = A.pointTransition (a 0).2.val (a 1).2.val p.val
      (A.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.logCover a 0 p.property))
      (A.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.logCover a 1 p.property)) :=
  A.logRefinement.refinement.exp_logarithm (a 0) (a 1)
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.cechIntersection_le_pair A.logCover a) p)

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.logCech_cocycle : LogCech.RationalCech.ExponentialCocycle
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) A.logCover A.logCech := by
  intro a p
  change Complex.exp (A.logCech (a ∘ (2 : Fin 3).succAbove) _) *
    Complex.exp (A.logCech (a ∘ (0 : Fin 3).succAbove) _) =
    Complex.exp (A.logCech (a ∘ (1 : Fin 3).succAbove) _)
  rw [A.exp_logCech, A.exp_logCech, A.exp_logCech]
  exact A.pointTransition_cocycle (a 0).2.val (a 1).2.val (a 2).2.val p.val
    (A.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.logCover a 0 p.property))
    (A.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.logCover a 1 p.property))
    (A.logCover_subset (a 2) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.logCover a 2 p.property))

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.logCech_firstChernClass : LogCech.RationalCech.logarithmicSingularClass
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) A.logCover A.logCover_covers A.logCech A.logCech_cocycle =
      First.firstChernClassQ P L :=
  A.firstChernClassQ_eq_on_cover A.logCover A.logCover_covers (fun a => a.2.val) A.logCover_subset
    A.logCech A.logCech_cocycle A.exp_logCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular
