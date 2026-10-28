import OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.AtlasIndependence
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # First -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.First

noncomputable section

/-!
# ChernClass: the rational first Chern class from actual line-bundle transitions

The construction takes algebraic section frames, evaluates their transition
units on analytic points, chooses a proved logarithmic cover refinement, and
maps the integral logarithmic defect to rational singular cohomology through
the actual Cech-to-singular comparison. No cohomology class or compatibility
identity is supplied as an input.

Independence of logarithms, analytic covers, and parent charts from the chosen
algebraic trivializing atlas is proved below. IsoClass separately proves
invariance under actual module-sheaf isomorphisms. Comparison with geometric
divisor classes remains to be proved; it is not a field or axiom.
-/

open _root_.CategoryTheory

/-- The rationalized exponential-sequence first Chern class of an actual
algebraic line bundle, computed using its analytic transition functions. -/
def firstChernClassQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Line.Bundles.AlgebraicLineBundle X → X.rationalCohomology 2 :=
  fun L => LogCech.RationalCech.logarithmicSingularClass
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover L.logCover_covers
    L.bundleLogCech L.bundleLogCech_cocycle

/-- Any continuous logarithms of the same transitions on this cover compute
the constructed class. -/
theorem firstChernClassQ_eq_of_logarithms (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L : Line.Bundles.AlgebraicLineBundle X)
    (l : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      L.logCover l)
    (he : ∀ (a : Fin 2 → L.LogCoverIndex) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a),
      Complex.exp (L.bundleLogCech a p) = Complex.exp (l a p)) :
    firstChernClassQ X L = LogCech.RationalCech.logarithmicSingularClass
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover L.logCover_covers l h :=
  LogCech.RationalCech.logarithmicSingularClass_log_independent
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover L.logCover_covers
    L.bundleLogCech l L.bundleLogCech_cocycle h he

/-- Further refinement of the constructed cover, with new logarithms of the
same transitions, computes the same rational first Chern class. -/
theorem firstChernClassQ_eq_on_refinement (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L : Line.Bundles.AlgebraicLineBundle X) {J : Type}
    (V : J → TopologicalSpace.Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
    (r : J → L.LogCoverIndex) (hr : ∀ j, V j ≤ L.logCover (r j))
    (hV : ∀ x, ∃ j, x ∈ V j)
    (l : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) V l)
    (he : ∀ (a : Fin 2 → J) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l a p) = Complex.exp
        (LogRefinement.RationalCech.refineLogCech (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
          L.logCover V r hr L.bundleLogCech a p)) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      V hV l h = firstChernClassQ X L :=
  LogRefinement.RationalCech.logarithmicSingularClass_refinement_of_exp_eq
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover V r hr
    L.logCover_covers hV L.bundleLogCech L.bundleLogCech_cocycle l h he

/-- Any logarithmic cover subordinate to the actual algebraic trivializing
atlas computes the same rational first Chern class. -/
theorem firstChernClassQ_eq_on_cover (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L : Line.Bundles.AlgebraicLineBundle X) {I : Type}
    (U : I → TopologicalSpace.Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
    (hU : ∀ x, ∃ i, x ∈ U i) (r : I → X.carrier)
    (hr : ∀ i, U i ≤ L.analyticCover (r i))
    (l : LogCech.RationalCech.LogCechCochain (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U)
    (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) U l)
    (he : ∀ (a : Fin 2 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = L.pointTransition (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))) :
    LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      U hU l h = firstChernClassQ X L := by
  apply L.logarithmicClass_cover_independent L.logCover L.logCover_covers U hU
    L.logParent r L.logCover_subset hr L.bundleLogCech l L.bundleLogCech_cocycle h
    _ he
  intro a p
  exact (L.exp_bundleLogCech a p).trans
    (L.pointTransition_eq_value (L.logParent ∘ a) 0 1
      ⟨p.val, L.logIntersection_subset a p.property⟩).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.First
