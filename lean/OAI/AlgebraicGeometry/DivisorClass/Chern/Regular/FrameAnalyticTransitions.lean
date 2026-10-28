import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingLineBundle
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineFrameTransition
import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedAnalyticFrames

/-! # Frame Analytic Transitions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameAnalyticTransitions

noncomputable section

section

/-! Explicit regular section frames for an actual algebraic line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

structure RegularSectionFrameAtlas {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (L : Line.Bundles.AlgebraicLineBundle P) (ι : Type) where
  domain : ι → P.carrier.Opens
  covers : iSup domain = ⊤
  frame : ∀ (i : ι) (W : P.carrier.Opens), W ≤ domain i →
    Γ(L.sheaf, W) ≃ₗ[Γ(P.carrier, W)] Γ(P.carrier, W)
  naturality : ∀ (i : ι) (W V : P.carrier.Opens) (hWi : W ≤ domain i) (hVW : V ≤ W)
    (s : Γ(L.sheaf, W)),
    frame i V (hVW.trans hWi) (L.sheaf.presheaf.map (homOfLE hVW).op s) =
      FunctionGluing.regularRestriction hVW (frame i W hWi s)

def regularCocycleSectionFrameAtlas (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {ι : Type}
    (D : FunctionGluing.RegularLineCocycle P.carrier ι) :
    RegularSectionFrameAtlas (LineBundle.regularCocycleAlgebraicLineBundle P D) ι where
  domain := D.domain
  covers := D.covers
  frame i W hi := LineSectionFrames.regularLineSectionLinearFrame D (U := W) i hi
  naturality i W V hi hVW s := LineSectionFrames.regularLineSectionFrameValue_restrict D (U := W) i hi (V := V) hVW s

namespace RegularSectionFrameAtlas
variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle P} {ι : Type}
  (A : RegularSectionFrameAtlas L ι)

def transition (i j : ι) (W : P.carrier.Opens) (hi : W ≤ A.domain i) (hj : W ≤ A.domain j) :
    Γ(P.carrier, W)ˣ := FramesFrame.Construction.frameTransitionUnit (A.frame i W hi) (A.frame j W hj)

theorem transition_restrict (i j : ι) (W V : P.carrier.Opens)
    (hi : W ≤ A.domain i) (hj : W ≤ A.domain j) (hVW : V ≤ W) :
    FunctionGluing.regularRestriction hVW (A.transition i j W hi hj : Γ(P.carrier, W)) =
      (A.transition i j V (hVW.trans hi) (hVW.trans hj) : Γ(P.carrier, V)) := by
  exact congrArg Units.val (FramesFrame.Construction.frameTransitionUnit_map (FunctionGluing.regularRestriction hVW)
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (A.frame i W hi) (A.frame j W hj)
    (A.frame i V (hVW.trans hi)) (A.frame j V (hVW.trans hj))
    (A.naturality i W V hi hVW) (A.naturality j W V hj hVW))

def mixedTransition (x : P.carrier) (i : ι) (W : P.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hi : W ≤ A.domain i) : Γ(P.carrier, W)ˣ :=
  FramesFrame.Construction.frameTransitionUnit (L.sectionFrame x W hx) (A.frame i W hi)

theorem mixedTransition_restrict (x : P.carrier) (i : ι) (W V : P.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hi : W ≤ A.domain i) (hVW : V ≤ W) :
    FunctionGluing.regularRestriction hVW (A.mixedTransition x i W hx hi : Γ(P.carrier, W)) =
      (A.mixedTransition x i V (hVW.trans hx) (hVW.trans hi) : Γ(P.carrier, V)) := by
  exact congrArg Units.val (FramesFrame.Construction.frameTransitionUnit_map (FunctionGluing.regularRestriction hVW)
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (L.sectionFrame x W hx) (A.frame i W hi)
    (L.sectionFrame x V (hVW.trans hx)) (A.frame i V (hVW.trans hi))
    (L.sectionFrame_naturality x hVW hx) (A.naturality i W V hi hVW))

theorem mixedTransition_square (x y : P.carrier) (i j : ι) (W : P.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (hi : W ≤ A.domain i) (hj : W ≤ A.domain j) :
    A.mixedTransition x i W hx hi * A.transition i j W hi hj =
      L.ambientTransitionOn x y W hx hy * A.mixedTransition y j W hy hj := by
  exact (FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _).trans
    (FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _).symm

end RegularSectionFrameAtlas

end

/-! Analytic evaluation of the actual explicit and mixed regular frame transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RegularSectionFrameAtlas
variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle P} {ι : Type}
  (A : RegularSectionFrameAtlas L ι)

abbrev analyticDomain (i : ι) : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) := Line.Bundles.AlgebraicLineBundle.analyticOpen P (A.domain i)

def transitionPair (i j : ι) : C((A.analyticDomain i ⊓ A.analyticDomain j :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)), ℂ) :=
  (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (A.domain i ⊓ A.domain j)
    (A.transition i j (A.domain i ⊓ A.domain j) inf_le_left inf_le_right :
      Γ(P.carrier, A.domain i ⊓ A.domain j))).comp
    ⟨fun p => ⟨p.val, p.property⟩, continuous_subtype_val.subtype_mk _⟩

abbrev pointTransition (i j : ι) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hi : p ∈ A.analyticDomain i) (hj : p ∈ A.analyticDomain j) : ℂ :=
  A.transitionPair i j ⟨p, hi, hj⟩

theorem pointTransition_restrict (i j : ι) (W : P.carrier.Opens)
    (hi : W ≤ A.domain i) (hj : W ≤ A.domain j) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen P W) :
    A.pointTransition i j p.val (hi p.property) (hj p.property) =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (A.transition i j W hi hj : Γ(P.carrier, W)) p := by
  have h := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict P (le_inf hi hj)
    (A.transition i j (A.domain i ⊓ A.domain j) inf_le_left inf_le_right :
      Γ(P.carrier, A.domain i ⊓ A.domain j)) p
  exact h.symm.trans (congrArg (fun r : Γ(P.carrier, W) => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W r p)
    (A.transition_restrict i j (A.domain i ⊓ A.domain j) W inf_le_left inf_le_right
      (le_inf hi hj)))

def mixedPair (x : P.carrier) (i : ι) :
    C((L.analyticCover x ⊓ A.analyticDomain i : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)), ℂ) :=
  (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (L.trivializingOpen x ⊓ A.domain i)
    (A.mixedTransition x i (L.trivializingOpen x ⊓ A.domain i) inf_le_left inf_le_right :
      Γ(P.carrier, L.trivializingOpen x ⊓ A.domain i))).comp
    ⟨fun p => ⟨p.val, p.property⟩, continuous_subtype_val.subtype_mk _⟩

abbrev mixedPointTransition (x : P.carrier) (i : ι) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hx : p ∈ L.analyticCover x) (hi : p ∈ A.analyticDomain i) : ℂ :=
  A.mixedPair x i ⟨p, hx, hi⟩

theorem mixedPair_ne_zero (x : P.carrier) (i : ι)
    (p : (L.analyticCover x ⊓ A.analyticDomain i : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver))) :
    A.mixedPair x i p ≠ 0 := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero P _ _ _

theorem mixedPointTransition_restrict (x : P.carrier) (i : ι) (W : P.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hi : W ≤ A.domain i) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen P W) :
    A.mixedPointTransition x i p.val (hx p.property) (hi p.property) =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (A.mixedTransition x i W hx hi : Γ(P.carrier, W)) p := by
  have h := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict P (le_inf hx hi)
    (A.mixedTransition x i (L.trivializingOpen x ⊓ A.domain i) inf_le_left inf_le_right :
      Γ(P.carrier, L.trivializingOpen x ⊓ A.domain i)) p
  exact h.symm.trans (congrArg (fun r : Γ(P.carrier, W) => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W r p)
    (A.mixedTransition_restrict x i (L.trivializingOpen x ⊓ A.domain i) W
      inf_le_left inf_le_right (le_inf hx hi)))

theorem mixedPointTransition_gauge (x y : P.carrier) (i j : ι) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hx : p ∈ L.analyticCover x) (hy : p ∈ L.analyticCover y)
    (hi : p ∈ A.analyticDomain i) (hj : p ∈ A.analyticDomain j) :
    A.pointTransition i j p hi hj = L.pointTransition x y p hx hy *
      A.mixedPointTransition y j p hy hj / A.mixedPointTransition x i p hx hi := by
  let W := (L.trivializingOpen x ⊓ L.trivializingOpen y) ⊓ (A.domain i ⊓ A.domain j)
  have hWx : W ≤ L.trivializingOpen x := inf_le_left.trans inf_le_left
  have hWy : W ≤ L.trivializingOpen y := inf_le_left.trans inf_le_right
  have hWi : W ≤ A.domain i := inf_le_right.trans inf_le_left
  have hWj : W ≤ A.domain j := inf_le_right.trans inf_le_right
  let q : Line.Bundles.AlgebraicLineBundle.analyticOpen P W := ⟨p, ⟨hx, hy⟩, ⟨hi, hj⟩⟩
  have h := congrArg (fun t : Γ(P.carrier, W)ˣ => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (t : Γ(P.carrier, W)) q)
    (A.mixedTransition_square x y i j W hWx hWy hWi hWj)
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W ((A.mixedTransition x i W hWx hWi : Γ(P.carrier, W)) *
      (A.transition i j W hWi hWj : Γ(P.carrier, W))) q =
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W ((L.ambientTransitionOn x y W hWx hWy : Γ(P.carrier, W)) *
      (A.mixedTransition y j W hWy hWj : Γ(P.carrier, W))) q at h
  rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul,
    ← A.mixedPointTransition_restrict, ← A.pointTransition_restrict,
    ← L.pointTransition_restrict, ← A.mixedPointTransition_restrict] at h
  apply (eq_div_iff (A.mixedPair_ne_zero x i ⟨p, hx, hi⟩)).mpr
  exact (mul_comm _ _).trans h

end RegularSectionFrameAtlas

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameAnalyticTransitions
