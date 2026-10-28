import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Coordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.Logarithms

/-! # Section Winding -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: supported winding of the actual rational-section coordinates

On the reference trivializing open, the actual rational section is a generator.
Its coordinates in each other algebraic frame are the already-constructed
transition units. Their continuous evaluation gives relative winding classes.
Changing the frame changes the equation by an actual ambient unit, so these
local relative classes agree. No geometric multiplicity comparison is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

/-- The part of an analytic algebraic open where the reference section is a generator. -/
def Line.Bundles.AlgebraicLineBundle.referenceLocus (W : X.carrier.Opens) : Set (Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :=
  {p | p.val ∈ Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen}

/-- Flatten the actual nested subspace to the analytic intersection. -/
def Line.Bundles.AlgebraicLineBundle.referenceLocusIntersectionMap (W : X.carrier.Opens) :
    C(L.referenceLocus W, Line.Bundles.AlgebraicLineBundle.analyticOpen X (W ⊓ L.rationalReferenceOpen)) :=
  ⟨fun p => ⟨p.val.val, p.val.property, p.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

/-- The equation on the reference locus is the actual unit whose generic germ
is the already-constructed rational-section coordinate. -/
def Line.Bundles.AlgebraicLineBundle.referenceEquation (i : X.carrier) (W : X.carrier.Opens) (hi : W ≤ L.trivializingOpen i) :
    C(L.referenceLocus W, ℂ) :=
  (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (W ⊓ L.rationalReferenceOpen)
    (L.ambientTransitionOn i (genericPoint X.carrier) (W ⊓ L.rationalReferenceOpen)
      (inf_le_left.trans hi) inf_le_right : Γ(X.carrier, W ⊓ L.rationalReferenceOpen))).comp
    (L.referenceLocusIntersectionMap W)

theorem Line.Bundles.AlgebraicLineBundle.referenceEquation_ne_zero (i : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (p : L.referenceLocus W) :
    L.referenceEquation i W hi p ≠ 0 :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

/-- The evaluated unit changing two actual algebraic frames on the whole open. -/
def Line.Bundles.AlgebraicLineBundle.frameChangeFunction (i j : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (hj : W ≤ L.trivializingOpen j) : C(Line.Bundles.AlgebraicLineBundle.analyticOpen X W, ℂ) :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (L.ambientTransitionOn i j W hi hj : Γ(X.carrier, W))

omit [IsIntegral X.carrier] in
theorem Line.Bundles.AlgebraicLineBundle.frameChangeFunction_ne_zero (i j : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (hj : W ≤ L.trivializingOpen j) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    L.frameChangeFunction i j W hi hj p ≠ 0 :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

/-- Actual analytic equation change, obtained from the algebraic transition cocycle. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceEquation_change (i j : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (hj : W ≤ L.trivializingOpen j) (p : L.referenceLocus W) :
    L.referenceEquation i W hi p =
      L.referenceEquation j W hj p * L.frameChangeFunction i j W hi hj p.val := by
  let V := W ⊓ L.rationalReferenceOpen
  have hVW : V ≤ W := inf_le_left
  have ht := congrArg Units.val (L.ambientTransitionOn_cocycle i j (genericPoint X.carrier) V
    (hVW.trans hi) (hVW.trans hj) inf_le_right)
  change (L.ambientTransitionOn i j V (hVW.trans hi) (hVW.trans hj) : Γ(X.carrier, V)) *
    (L.ambientTransitionOn j (genericPoint X.carrier) V (hVW.trans hj) inf_le_right : Γ(X.carrier, V)) =
    (L.ambientTransitionOn i (genericPoint X.carrier) V (hVW.trans hi) inf_le_right : Γ(X.carrier, V)) at ht
  have hr := congrArg Units.val (L.ambientTransitionOn_restrict i j hVW hi hj)
  change X.carrier.presheaf.map (homOfLE hVW).op (L.ambientTransitionOn i j W hi hj : Γ(X.carrier, W)) =
    (L.ambientTransitionOn i j V (hVW.trans hi) (hVW.trans hj) : Γ(X.carrier, V)) at hr
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X V _ (L.referenceLocusIntersectionMap W p) =
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X V _ (L.referenceLocusIntersectionMap W p) * Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W _ p.val
  rw [← ht, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, ← hr, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict]
  exact mul_comm _ _

/-- The actual relative class of the rational section in one algebraic frame. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass (i : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Line.Bundles.AlgebraicLineBundle.analyticOpen X W))
      (L.referenceLocus W) 2 :=
  Supported.Winding.supportedWindingClass (TopCat.of (Line.Bundles.AlgebraicLineBundle.analyticOpen X W)) (L.referenceLocus W)
    (L.referenceEquation i W hi) (L.referenceEquation_ne_zero i W hi)

/-- The relative class does not depend on the algebraic frame used to compute it. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass_frame_independent (i j : X.carrier)
    (W : X.carrier.Opens) (hi : W ≤ L.trivializingOpen i) (hj : W ≤ L.trivializingOpen j) :
    L.rationalSectionLocalSupportedClass i W hi = L.rationalSectionLocalSupportedClass j W hj := by
  have he : L.referenceEquation i W hi = L.referenceEquation j W hj *
      (L.frameChangeFunction i j W hi hj).comp ⟨Subtype.val, continuous_subtype_val⟩ :=
    ContinuousMap.ext (L.referenceEquation_change i j W hi hj)
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass
  refine (Supported.Winding.supportedWindingClass_congr _ _ _ _ _
    (fun p => mul_ne_zero (L.referenceEquation_ne_zero j W hj p)
      (L.frameChangeFunction_ne_zero i j W hi hj p.val)) he).trans ?_
  exact Supported.Winding.supportedWindingClass_mul_extending_unit (TopCat.of (Line.Bundles.AlgebraicLineBundle.analyticOpen X W)) (L.referenceLocus W)
    (L.referenceEquation j W hj) (L.referenceEquation_ne_zero j W hj)
    (L.frameChangeFunction i j W hi hj) (L.frameChangeFunction_ne_zero i j W hi hj)

/-- The regular coordinate used here has exactly the existing rational-section germ. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceEquation_genericCoordinate (i : X.carrier) (W : X.carrier.Opens)
    [Nonempty (W ⊓ L.rationalReferenceOpen : X.carrier.Opens)] (hi : W ≤ L.trivializingOpen i) :
    L.genericTransitionUnit i (genericPoint X.carrier) (W ⊓ L.rationalReferenceOpen)
      (inf_le_left.trans hi) inf_le_right = L.rationalSectionCoordinate i := by
  have h : W ⊓ L.rationalReferenceOpen ≤ L.rationalCoordinateDomain i :=
    le_inf (inf_le_left.trans hi) inf_le_right
  exact L.genericTransitionUnit_restrict i (genericPoint X.carrier) h inf_le_left inf_le_right

/-- Restriction of the equation is actual restriction of the same algebraic transition unit. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceEquation_restrict (i : X.carrier) {V W : X.carrier.Opens} (hVW : V ≤ W)
    (hi : W ≤ L.trivializingOpen i) (p : L.referenceLocus V) :
    L.referenceEquation i V (hVW.trans hi) p =
      L.referenceEquation i W hi ⟨⟨p.val.val, hVW p.val.property⟩, p.property⟩ := by
  have h : V ⊓ L.rationalReferenceOpen ≤ W ⊓ L.rationalReferenceOpen := inf_le_inf_right _ hVW
  have hr := congrArg Units.val (L.ambientTransitionOn_restrict i (genericPoint X.carrier) h
    (inf_le_left.trans hi) inf_le_right)
  change X.carrier.presheaf.map (homOfLE h).op
      (L.ambientTransitionOn i (genericPoint X.carrier) (W ⊓ L.rationalReferenceOpen)
        (inf_le_left.trans hi) inf_le_right : Γ(X.carrier, W ⊓ L.rationalReferenceOpen)) =
    (L.ambientTransitionOn i (genericPoint X.carrier) (V ⊓ L.rationalReferenceOpen)
      (inf_le_left.trans (hVW.trans hi)) inf_le_right : Γ(X.carrier, V ⊓ L.rationalReferenceOpen)) at hr
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (V ⊓ L.rationalReferenceOpen) _ _ =
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (W ⊓ L.rationalReferenceOpen) _ _
  rw [← hr, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict]
  rfl

/-- The analytic inclusion of two algebraic opens, written with its actual source and target. -/
def Line.Bundles.AlgebraicLineBundle.referenceAmbientInclusion {V W : X.carrier.Opens} (hVW : V ≤ W) :
    TopCat.of (Line.Bundles.AlgebraicLineBundle.analyticOpen X V) ⟶ TopCat.of (Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :=
  TopCat.ofHom (LogRefinementOpen.Construction.openInclusionMap (show Line.Bundles.AlgebraicLineBundle.analyticOpen X V ≤ Line.Bundles.AlgebraicLineBundle.analyticOpen X W from fun _ hp => hVW hp))

/-- The analytic inclusion is a map of the actual reference-locus pairs. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceAmbientInclusion_mapsTo {V W : X.carrier.Opens} (hVW : V ≤ W) :
    Set.MapsTo (Line.Bundles.AlgebraicLineBundle.referenceAmbientInclusion hVW) (L.referenceLocus V) (L.referenceLocus W) :=
  fun _ hp => hp

/-- The frame-independent local supported classes also commute with open restriction. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass_restrict (i : X.carrier) {V W : X.carrier.Opens}
    (hVW : V ≤ W) (hi : W ≤ L.trivializingOpen i) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Line.Bundles.AlgebraicLineBundle.referenceAmbientInclusion hVW)
        (L.referenceAmbientInclusion_mapsTo hVW) 2 (L.rationalSectionLocalSupportedClass i W hi) =
      L.rationalSectionLocalSupportedClass i V (hVW.trans hi) := by
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass
  rw [Supported.Winding.supportedWindingClass_pullback]
  apply Supported.Winding.supportedWindingClass_congr
  apply ContinuousMap.ext
  intro p
  exact (L.referenceEquation_restrict i hVW hi p).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
