import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FlasqueComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparison

/-! # Local Equations -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations

noncomputable section

/-!
# ChernClass: actual Chern restrictions on every algebraic frame neighborhood

The canonical section comparison is invertible on every analytic open by
the proved reference-support purity. Thus the genuine global relative Chern
class restricts to the actual rational-section equation on any such open.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) := by
  let V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨X, inferInstance⟩
  exact inferInstanceAs (MetrizableSpace V.analyticSpace)

/-- The actual relative-to-supported-section map is invertible on every
analytic open in degree two. -/
instance _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceSectionMap_isIso (U : Opens T) :
    IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U 2) := by
  rw [CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_def]
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ T O U
  have := Open.FlasqueComparison.rationalFlasqueOpenSectionMap_isIso U L.rationalSectionSupportComplex
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) T O) 2
    (fun n hn => CycleClass.Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_exactAt_of_stalk_isZero L.rationalSectionSupportComplex n
      (fun x => L.referenceSupportedStalk_isZero x n hn))
  infer_instance

/-- Restricting the genuine relative Chern class to any analytic frame
neighborhood gives the winding of the same rational-section equation. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_restrictOn (i : X.carrier) (U : Opens T)
    (hi : U ≤ L.analyticCover i) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) U 2
      L.rationalSectionChernRelativeClass =
    Supported.Winding.supportedWindingClass (TopCat.of U) (L.analyticReferenceLocus U)
      (L.referenceEquationOn i U hi) (L.referenceEquationOn_ne_zero i U hi) := by
  apply (ModuleCat.mono_iff_injective
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U 2)).mp inferInstance
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O U 2)
    L.rationalSectionChernRelativeClass
  change ((L.rationalSectionSupportComplex.homology 2).obj).map
      (homOfLE (le_top : U ≤ ⊤)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 L.rationalSectionChernRelativeClass) = _ at h
  rw [L.rationalSectionChernRelativeClass_eq_supported,
    L.rationalSectionSupportedClass_section] at h
  rw [L.rationalSectionChernRelativeClass_eq_supported]
  exact h.symm.trans (L.rationalSectionSupportedSection_restrictOn i U hi)

/-- On every algebraic frame neighborhood the actual global Chern lift
restricts to the previously defined local rational-section class. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_algebraic (i : X.carrier) (U : X.carrier.Opens)
    (hi : U ≤ L.trivializingOpen i) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
      L.rationalSectionChernRelativeClass = L.rationalSectionLocalSupportedClass i U hi := by
  rw [L.rationalSectionChernRelativeClass_restrictOn i (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (fun _ hx => hi hx)]
  apply Supported.Winding.supportedWindingClass_congr
  apply ContinuousMap.ext
  intro p
  exact L.referenceEquationOn_algebraic i U hi (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) le_rfl p

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations
