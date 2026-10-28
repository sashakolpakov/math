import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionWinding
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cocycle
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Section Gluing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: gluing the actual rational-section supported classes

The local classes computed from algebraic rational-section coordinates define
compatible sections of the genuine supported cohomology sheaf. The sheaf
axiom glues these to one global section, with proved restrictions to the
algebraic trivializing cover. No raw-cohomology descent assumption is made.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [AlgebraicGeometry.IsIntegral X.carrier]

/-- The actual supported singular cochain complex for the reference-open complement. -/
abbrev Line.Bundles.AlgebraicLineBundle.rationalSectionSupportComplex :=
  CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
    (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen)

/-- Image of the constructed relative class in the genuine supported cohomology sheaf. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSection (i : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) :
    (L.rationalSectionSupportComplex.homology 2).obj.obj (op (Line.Bundles.AlgebraicLineBundle.analyticOpen X W)) :=
  CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
    (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) (Line.Bundles.AlgebraicLineBundle.analyticOpen X W) 2
    (L.rationalSectionLocalSupportedClass i W hi)

/-- Restricting this section is the section of the genuinely restricted local class. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSection_restrict (i : X.carrier) {V W : X.carrier.Opens}
    (hVW : V ≤ W) (hi : W ≤ L.trivializingOpen i) :
    (L.rationalSectionSupportComplex.homology 2).obj.map
        (homOfLE (show Line.Bundles.AlgebraicLineBundle.analyticOpen X V ≤ Line.Bundles.AlgebraicLineBundle.analyticOpen X W from fun _ hp => hVW hp)).op
        (L.rationalSectionLocalSection i W hi) =
      L.rationalSectionLocalSection i V (hVW.trans hi) := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_naturality (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen)
      (homOfLE (show Line.Bundles.AlgebraicLineBundle.analyticOpen X V ≤ Line.Bundles.AlgebraicLineBundle.analyticOpen X W from fun _ hp => hVW hp)) 2)
    (L.rationalSectionLocalSupportedClass i W hi)
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) (Line.Bundles.AlgebraicLineBundle.analyticOpen X V) 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Line.Bundles.AlgebraicLineBundle.referenceAmbientInclusion hVW)
        (L.referenceAmbientInclusion_mapsTo hVW) 2 (L.rationalSectionLocalSupportedClass i W hi)) = _ at h
  rw [L.rationalSectionLocalSupportedClass_restrict] at h
  exact h.symm

/-- The section has no dependence on the algebraic frame. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSection_frame_independent (i j : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (hj : W ≤ L.trivializingOpen j) :
    L.rationalSectionLocalSection i W hi = L.rationalSectionLocalSection j W hj := by
  unfold Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSection
  rw [L.rationalSectionLocalSupportedClass_frame_independent i j W hi hj]

/-- The sections on the actual trivializing cover agree on overlaps. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSections_compatible :
    TopCat.Presheaf.IsCompatible (L.rationalSectionSupportComplex.homology 2).obj L.analyticCover
      (fun i => L.rationalSectionLocalSection i (L.trivializingOpen i) le_rfl) := by
  intro i j
  have hi := L.rationalSectionLocalSection_restrict i
    (show L.trivializingOpen i ⊓ L.trivializingOpen j ≤ L.trivializingOpen i from inf_le_left) le_rfl
  have hj := L.rationalSectionLocalSection_restrict j
    (show L.trivializingOpen i ⊓ L.trivializingOpen j ≤ L.trivializingOpen j from inf_le_right) le_rfl
  exact hi.trans ((L.rationalSectionLocalSection_frame_independent i j
    (L.trivializingOpen i ⊓ L.trivializingOpen j) inf_le_left inf_le_right).trans hj.symm)

omit [AlgebraicGeometry.IsIntegral X.carrier] in
/-- The genuine analytic trivializing family covers the top open. -/
theorem Line.Bundles.AlgebraicLineBundle.analyticCover_iSup_eq_top : iSup L.analyticCover = ⊤ := by
  apply top_unique
  intro p _
  exact Opens.mem_iSup.mpr (L.analyticCover_covers p)

/-- The actual local relative classes glue uniquely after passing to the
supported cohomology sheaf. -/
theorem Line.Bundles.AlgebraicLineBundle.existsUnique_rationalSectionSupportedSection :
    ∃! s : (L.rationalSectionSupportComplex.homology 2).obj.obj (op (⊤ : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))),
      ∀ i, (L.rationalSectionSupportComplex.homology 2).obj.map
        (homOfLE (le_top : L.analyticCover i ≤ ⊤)).op s =
        L.rationalSectionLocalSection i (L.trivializingOpen i) le_rfl :=
  CycleClass.Geometric.RelativeCohomologySections.Cycles.existsUnique_relativeCohomologyGlobalSection (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen)
    L.analyticCover L.analyticCover_iSup_eq_top 2
    (fun i => L.rationalSectionLocalSupportedClass i (L.trivializingOpen i) le_rfl)
    L.rationalSectionLocalSections_compatible

/-- The resulting global section is built from the same actual rational section of the bundle. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionSupportedSection :
    (L.rationalSectionSupportComplex.homology 2).obj.obj (op (⊤ : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) :=
  L.existsUnique_rationalSectionSupportedSection.choose

theorem Line.Bundles.AlgebraicLineBundle.rationalSectionSupportedSection_restrict (i : X.carrier) :
    (L.rationalSectionSupportComplex.homology 2).obj.map
        (homOfLE (le_top : L.analyticCover i ≤ ⊤)).op L.rationalSectionSupportedSection =
      L.rationalSectionLocalSection i (L.trivializingOpen i) le_rfl :=
  L.existsUnique_rationalSectionSupportedSection.choose_spec.1 i

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
