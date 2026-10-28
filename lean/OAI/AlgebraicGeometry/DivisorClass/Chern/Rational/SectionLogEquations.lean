import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionWinding
import OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingSingular

/-! # Section Log Equations -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionLogEquations

noncomputable section

/-!
# ChernClass: rational-section equations on the actual logarithmic cover

The equations below restrict the already constructed algebraic rational
section. On the logarithmic cover their ratios are the exponentials of the
same transition logarithms used to define `firstChernClassQ`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)

/-- The reference locus inside an arbitrary analytic open. -/
abbrev _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticReferenceLocus (U : Opens T) : Set U :=
  AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) U

/-- Restrict the actual algebraic rational-section equation to an analytic open. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceEquationOn (i : X.carrier) (U : Opens T) (hi : U ≤ L.analyticCover i) :
    C(L.analyticReferenceLocus U, ℂ) :=
  (L.referenceEquation i (L.trivializingOpen i) le_rfl).comp
    ⟨fun p => ⟨⟨p.val.val, hi p.val.property⟩, p.property⟩,
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceEquationOn_ne_zero (i : X.carrier) (U : Opens T)
    (hi : U ≤ L.analyticCover i) (p : L.analyticReferenceLocus U) :
    L.referenceEquationOn i U hi p ≠ 0 :=
  L.referenceEquation_ne_zero i (L.trivializingOpen i) le_rfl _

/-- The analytic equation agrees with every smaller algebraic representative. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceEquationOn_algebraic (i : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (U : Opens T) (hU : U ≤ Line.Bundles.AlgebraicLineBundle.analyticOpen X W)
    (p : L.analyticReferenceLocus U) :
    L.referenceEquationOn i U (fun _ hx => hi (hU hx)) p =
      L.referenceEquation i W hi ⟨⟨p.val.val, hU p.val.property⟩, p.property⟩ := by
  have h := L.referenceEquation_restrict i (V := W) (W := L.trivializingOpen i) hi le_rfl
    (show L.referenceLocus W from ⟨⟨p.val.val, hU p.val.property⟩, p.property⟩)
  exact h.symm

/-- Restricting to a smaller analytic open changes only the domain. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceEquationOn_restrict (i : X.carrier) {U V : Opens T}
    (hUV : U ≤ V) (hi : V ≤ L.analyticCover i) (p : L.analyticReferenceLocus U) :
    L.referenceEquationOn i U (hUV.trans hi) p =
      L.referenceEquationOn i V hi ⟨⟨p.val.val, hUV p.val.property⟩, p.property⟩ := rfl

/-- On an analytic intersection the equation ratio is the actual algebraic transition. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceEquationOn_change (a : Fin 2 → X.carrier) (U : Opens T)
    (hU : U ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) (p : L.analyticReferenceLocus U) :
    L.referenceEquationOn (a 0) U (hU.trans (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.analyticCover a 0)) p =
      L.referenceEquationOn (a 1) U (hU.trans (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.analyticCover a 1)) p *
        L.transitionCech a ⟨p.val.val, hU p.val.property⟩ := by
  let W := L.algebraicIntersection a
  have hW : U ≤ Line.Bundles.AlgebraicLineBundle.analyticOpen X W := by
    intro x hx
    exact (L.intersectionPointMap a ⟨x, hU hx⟩).property
  have he₀ := L.referenceEquationOn_algebraic (a 0) W
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 0) U hW p
  have he₁ := L.referenceEquationOn_algebraic (a 1) W
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 1) U hW p
  rw [he₀, he₁, L.referenceEquation_change]
  rfl

/-- Each local reference equation on the same refined cover used for the Chern class. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logReferenceEquation (a : L.LogCoverIndex) :
    C(L.analyticReferenceLocus (L.logCover a), ℂ) :=
  L.referenceEquationOn (L.logParent a) (L.logCover a) (L.logCover_subset a)

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logReferenceEquation_ne_zero (a : L.LogCoverIndex)
    (p : L.analyticReferenceLocus (L.logCover a)) :
    L.logReferenceEquation a p ≠ 0 :=
  L.referenceEquationOn_ne_zero _ _ _ p

/-- All local equations may be restricted to any finite logarithmic intersection. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logIntersectionEquation {n : ℕ} (a : Fin (n + 1) → L.LogCoverIndex) (k : Fin (n + 1)) :
    C(L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a), ℂ) :=
  L.referenceEquationOn (L.logParent (a k)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)
    ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a k).trans (L.logCover_subset (a k)))

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logIntersectionEquation_ne_zero {n : ℕ} (a : Fin (n + 1) → L.LogCoverIndex)
    (k : Fin (n + 1)) (p : L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)) :
    L.logIntersectionEquation a k p ≠ 0 := L.referenceEquationOn_ne_zero _ _ _ p

/-- Restriction of the Chern transition logarithm to the actual reference locus. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logReferenceTransition (a : Fin 2 → L.LogCoverIndex) :
    C(L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a), ℂ) :=
  (L.bundleLogCech a).comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The constructed equations and the constructed Chern logarithms agree exactly. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logReferenceTransition_equation (a : Fin 2 → L.LogCoverIndex)
    (p : L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)) :
    Complex.exp (L.logReferenceTransition a p) * L.logIntersectionEquation a 1 p =
      L.logIntersectionEquation a 0 p := by
  have h := L.referenceEquationOn_change (L.logParent ∘ a)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) (L.logIntersection_subset a) p
  change L.logIntersectionEquation a 0 p = L.logIntersectionEquation a 1 p *
    L.transitionCech (L.logParent ∘ a) ⟨p.val.val, L.logIntersection_subset a p.val.property⟩ at h
  change Complex.exp (L.bundleLogCech a p.val) * L.logIntersectionEquation a 1 p = _
  rw [L.exp_bundleLogCech]
  exact (mul_comm _ _).trans h.symm

/-- The actual zero-cochain correction on a pairwise overlap of reference loci. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logReferenceGaugePrimitive (a : Fin 2 → L.LogCoverIndex) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)))).X 0 :=
  WindingSingular.windingGaugePrimitive _ (L.logIntersectionEquation a 0) (L.logIntersectionEquation a 1)
    (L.logIntersectionEquation_ne_zero a 0) (L.logIntersectionEquation_ne_zero a 1)
    (L.logReferenceTransition a) (L.logReferenceTransition_equation a)

/-- Its differential is the difference of the winding cochains of the actual section. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logReferenceGaugePrimitive_d (a : Fin 2 → L.LogCoverIndex) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)))).d 0 1
        (L.logReferenceGaugePrimitive a) =
      WindingSingular.singularWindingCochain _ (L.logIntersectionEquation a 0) (L.logIntersectionEquation_ne_zero a 0) -
        WindingSingular.singularWindingCochain _ (L.logIntersectionEquation a 1) (L.logIntersectionEquation_ne_zero a 1) :=
  WindingSingular.windingGaugePrimitive_d _ _ _ _ _ _ _

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionLogEquations
