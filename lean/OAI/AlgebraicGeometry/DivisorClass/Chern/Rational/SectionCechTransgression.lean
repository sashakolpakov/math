import OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionLogEquations

/-! # Section Cech Transgression -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionCechTransgression

noncomputable section

/-!
# ChernClass: Cech transgression of the actual rational-section equations

Winding of the section coordinates and the integer corrections between
coordinates occupy bidegrees `(0,1)` and `(1,0)` over the reference locus.
Their differentials are the exact compatibility identities required to lift
the constructed Chern cocycle to relative cochains.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "A" => (OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T)
local notation "K" => OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD.RationalCech.subspaceSingularPresheafComplex T A

/-- The actual reference-subspace inclusion, with explicit source and target. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceSubspaceInclusion {U V : Opens T} (hUV : U ≤ V) :
    TopCat.of (L.analyticReferenceLocus U) ⟶ TopCat.of (L.analyticReferenceLocus V) :=
  TopCat.ofHom ⟨fun p => ⟨⟨p.val.val, hUV p.val.property⟩, p.property⟩,
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.singularWindingCochain_congr (Y : TopCat.{0}) (f g : C(Y, ℂ))
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) (hfg : f = g) :
    WindingSingular.singularWindingCochain Y f hf = WindingSingular.singularWindingCochain Y g hg := by
  subst g
  rfl

/-- Restricting an actual coordinate winding cochain only restricts its equation. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.logIntersectionWinding_restrict {n m : ℕ}
    (a : Fin (m + 1) → L.LogCoverIndex) (r : Fin (n + 1) → Fin (m + 1)) (k : Fin (n + 1)) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
      (L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a r))).f 1
      (WindingSingular.singularWindingCochain _ (L.logIntersectionEquation (a ∘ r) k)
        (L.logIntersectionEquation_ne_zero (a ∘ r) k)) =
    WindingSingular.singularWindingCochain _ (L.logIntersectionEquation a (r k))
      (L.logIntersectionEquation_ne_zero a (r k)) := by
  have h := WindingSingular.singularWindingCochain_naturality
    (L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a r))
    (L.logIntersectionEquation (a ∘ r) k) (L.logIntersectionEquation_ne_zero (a ∘ r) k)
  refine h.trans (Line.Bundles.AlgebraicLineBundle.singularWindingCochain_congr _ _ _ _ _ ?_)
  apply ContinuousMap.ext
  intro p
  rfl

/-- The winding cochains of the actual section coordinates on singleton intersections. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceWindingCech : Cech.RationalCech.CechCochain (SubspaceCechD.RationalCech.subspaceSingularDegreePresheaf T A 1) L.logCover 0 :=
  fun a => WindingSingular.singularWindingCochain _ (L.logIntersectionEquation a 0)
    (L.logIntersectionEquation_ne_zero a 0)

/-- The actual integer zero-cochain corrections between the local equations. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceGaugeCech : Cech.RationalCech.CechCochain (SubspaceCechD.RationalCech.subspaceSingularDegreePresheaf T A 0) L.logCover 1 :=
  L.logReferenceGaugePrimitive

/-- Each coordinate winding cochain is closed before any gluing. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceWindingCech_vertical :
    Cech.RationalCech.cechCoefficientMap L.logCover ((K).d 1 2) 0 L.referenceWindingCech = 0 := by
  funext a
  exact (SubspaceCechD.RationalCech.subspaceCechVertical_apply T A L.logCover 0 1 L.referenceWindingCech a).trans
    (WindingSingular.singularWindingCochain_closed
      (TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)))
      (L.logIntersectionEquation a 0) (L.logIntersectionEquation_ne_zero a 0))

/-- The horizontal mismatch between coordinate windings is the negative
vertical differential of their actual correction. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceWindingCech_horizontal :
    Cech.RationalCech.cechDelta ((K).X 1) L.logCover 0 L.referenceWindingCech =
      -Cech.RationalCech.cechCoefficientMap L.logCover ((K).d 0 1) 1 L.referenceGaugeCech := by
  funext a
  rw [Cech.RationalCech.cechDelta_apply, Fin.sum_univ_two]
  let f₀ := L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a (0 : Fin 2).succAbove)
  let f₁ := L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a (1 : Fin 2).succAbove)
  change (1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f₀).f 1
      (WindingSingular.singularWindingCochain
        (TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover (a ∘ (0 : Fin 2).succAbove))))
        (L.logIntersectionEquation (a ∘ (0 : Fin 2).succAbove) 0)
        (L.logIntersectionEquation_ne_zero (a ∘ (0 : Fin 2).succAbove) 0)) +
    (-1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f₁).f 1
      (WindingSingular.singularWindingCochain
        (TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover (a ∘ (1 : Fin 2).succAbove))))
        (L.logIntersectionEquation (a ∘ (1 : Fin 2).succAbove) 0)
        (L.logIntersectionEquation_ne_zero (a ∘ (1 : Fin 2).succAbove) 0)) =
    -((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)))).d 0 1
        (L.logReferenceGaugePrimitive a))
  rw [one_zsmul, neg_one_zsmul]
  have h₀ := L.logIntersectionWinding_restrict a (0 : Fin 2).succAbove 0
  have h₁ := L.logIntersectionWinding_restrict a (1 : Fin 2).succAbove 0
  rw [h₀, h₁, L.logReferenceGaugePrimitive_d]
  rw [show (0 : Fin 2).succAbove 0 = 1 from rfl,
    show (1 : Fin 2).succAbove 0 = 0 from rfl]
  abel

/-- The triple-overlap sum is the restriction of the very Chern defect used
in the public first Chern class construction. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceGaugeCech_horizontal :
    Cech.RationalCech.cechDelta ((K).X 0) L.logCover 1 L.referenceGaugeCech =
      SubspaceCechD.RationalCech.subspaceCechRestriction T A L.logCover 2 0
        (Cech.Obj.RationalCech.locallyConstantCechEvaluation T L.logCover 2
          (LogCech.RationalCech.logDefectCech T L.logCover L.bundleLogCech L.bundleLogCech_cocycle)) := by
  funext a
  let Y := TopCat.of (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
  apply (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) Y).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) Y).hom _ =
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) Y).hom _
  ext x
  rw [Cech.RationalCech.cechDelta_apply, Fin.sum_univ_three]
  let f₀ := L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a (0 : Fin 3).succAbove)
  let f₁ := L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a (1 : Fin 3).succAbove)
  let f₂ := L.referenceSubspaceInclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.logCover a (2 : Fin 3).succAbove)
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) Y).hom
    ((1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f₀).f 0
      (L.logReferenceGaugePrimitive (a ∘ (0 : Fin 3).succAbove)) +
    (-1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f₁).f 0
      (L.logReferenceGaugePrimitive (a ∘ (1 : Fin 3).succAbove)) +
    (1 : ℤ) • (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f₂).f 0
      (L.logReferenceGaugePrimitive (a ∘ (2 : Fin 3).succAbove))) x =
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) Y).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
          (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)))).f 0
          (AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero (ModuleCat.of ℚ ℚ) _
            (LogCech.RationalCech.logDefectCech T L.logCover L.bundleLogCech L.bundleLogCech_cocycle a))) x
  rw [one_zsmul, one_zsmul, neg_one_zsmul, map_add, map_add, map_neg]
  dsimp only [Pi.add_apply, Pi.neg_apply]
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback,
    AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_pullback,
    AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply]
  unfold Line.Bundles.AlgebraicLineBundle.logReferenceGaugePrimitive
  rw [WindingSingular.windingGaugePrimitive_value, WindingSingular.windingGaugePrimitive_value, WindingSingular.windingGaugePrimitive_value]
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  push_cast
  rw [add_mul, add_mul, neg_mul, WindingSingular.windingGaugePeriod_spec, WindingSingular.windingGaugePeriod_spec,
    WindingSingular.windingGaugePeriod_spec]
  change _ = (((Logarithms.Construction.logarithmicDefect _ _ _ (L.bundleLogCech_cocycle a x.val) : ℤ) : ℚ) : ℂ) * _
  push_cast
  rw [← Logarithms.Construction.logarithmicDefect_spec]
  change (L.logReferenceTransition (a ∘ (0 : Fin 3).succAbove) (f₀ x) +
      Complex.log (L.logIntersectionEquation a 2 x) - Complex.log (L.logIntersectionEquation a 1 x)) +
    -(L.logReferenceTransition (a ∘ (1 : Fin 3).succAbove) (f₁ x) +
      Complex.log (L.logIntersectionEquation a 2 x) - Complex.log (L.logIntersectionEquation a 0 x)) +
    (L.logReferenceTransition (a ∘ (2 : Fin 3).succAbove) (f₂ x) +
      Complex.log (L.logIntersectionEquation a 1 x) - Complex.log (L.logIntersectionEquation a 0 x)) =
    _
  change _ = L.logReferenceTransition (a ∘ (2 : Fin 3).succAbove) (f₂ x) +
    L.logReferenceTransition (a ∘ (0 : Fin 3).succAbove) (f₀ x) -
    L.logReferenceTransition (a ∘ (1 : Fin 3).succAbove) (f₁ x)
  ring

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionCechTransgression
