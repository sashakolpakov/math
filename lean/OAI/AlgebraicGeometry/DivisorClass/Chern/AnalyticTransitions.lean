import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Analytic Transitions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: regular transition functions on complex points

Evaluation is induced by the actual complex point's map on global sections.
Continuity is proved using the existing affine-test topology. Applied to
the line-bundle transition units, this gives nonvanishing continuous complex
functions with the multiplicative cocycle identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AnalyticTransitions.Construction

/-- The ring homomorphism evaluating global regular functions at a complex point. -/
def globalSectionEvaluation {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Γ(X.left, ⊤) →+* ℂ :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom.comp p.left.appTop.hom

/-- Evaluation commutes with pullback of global regular functions. -/
theorem globalSectionEvaluation_map
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (s : Γ(Y.left, ⊤)) :
    globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) s =
      globalSectionEvaluation p (f.left.appTop s) := rfl

/-- On an affine scheme this is the usual evaluation of a character. -/
theorem globalSectionEvaluation_affine
    (A : Type) [CommRing A] [Algebra ℂ A]
    (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (s : Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤)) :
    globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A p) s =
      p ((Scheme.ΓSpecIso (CommRingCat.of A)).hom s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p).left.appTop s) = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom p.toRingHom)) s

/-- Global regular functions are continuous in the actual analytic topology. -/
theorem continuous_globalSectionEvaluation
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) :
    Continuous (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => globalSectionEvaluation p s) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A f
  have h : (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
      globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f p) s) =
      (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
        p ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (f.left.appTop s))) := by
    funext p
    exact globalSectionEvaluation_affine A p (f.left.appTop s)
  rw [h]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval _

/-- A global algebraic unit evaluates to a nonzero complex number. -/
theorem globalSectionEvaluation_unit_ne_zero
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u : Γ(X.left, ⊤)ˣ) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    globalSectionEvaluation p (u : Γ(X.left, ⊤)) ≠ 0 :=
  (u.isUnit.map (globalSectionEvaluation p)).ne_zero

/-- A global regular function as a bundled continuous function on complex points. -/
def globalSectionContinuousMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) :
    C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ) :=
  ⟨fun p => globalSectionEvaluation p s, continuous_globalSectionEvaluation X s⟩

end AnalyticTransitions.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- An open subscheme with the complex structure inherited from X. -/
abbrev Line.Bundles.AlgebraicLineBundle.openOver (W : X.carrier.Opens) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (W.ι ≫ X.structureMap)

/-- Evaluate the actual transition unit on the complex points of a common open. -/
def Line.Bundles.AlgebraicLineBundle.analyticTransitionOn (x y : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W), ℂ) :=
  AnalyticTransitions.Construction.globalSectionContinuousMap (Line.Bundles.AlgebraicLineBundle.openOver W)
    (L.transitionOn x y W hx hy : Γ(W.toScheme, ⊤))

theorem Line.Bundles.AlgebraicLineBundle.analyticTransitionOn_ne_zero (x y : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W)) :
    L.analyticTransitionOn x y W hx hy p ≠ 0 := by
  change AnalyticTransitions.Construction.globalSectionEvaluation p
    (L.transitionOn x y W hx hy : Γ(W.toScheme, ⊤)) ≠ 0
  exact AnalyticTransitions.Construction.globalSectionEvaluation_unit_ne_zero
    (X := Line.Bundles.AlgebraicLineBundle.openOver W) (L.transitionOn x y W hx hy) p

/-- The algebraic cocycle remains a cocycle after actual complex-point evaluation. -/
theorem Line.Bundles.AlgebraicLineBundle.analyticTransitionOn_cocycle (x y z : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (hz : W ≤ L.trivializingOpen z)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W)) :
    L.analyticTransitionOn x y W hx hy p * L.analyticTransitionOn y z W hy hz p =
      L.analyticTransitionOn x z W hx hz p := by
  change AnalyticTransitions.Construction.globalSectionEvaluation p _ * AnalyticTransitions.Construction.globalSectionEvaluation p _ =
    AnalyticTransitions.Construction.globalSectionEvaluation p _
  rw [← map_mul]
  exact congrArg (fun u : Γ(W.toScheme, ⊤)ˣ =>
    AnalyticTransitions.Construction.globalSectionEvaluation p (u : Γ(W.toScheme, ⊤)))
    (L.transitionOn_cocycle x y z W hx hy hz)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
