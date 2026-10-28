import OAI.AlgebraicGeometry.DivisorClass.Chern.ReferenceStratification
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ImmersionPurity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.SupportFiltration
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # Reference Purity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ReferencePurity

noncomputable section

/-!
# ChernClass: low-degree purity of the actual reference complement

Every smooth stratum has real codimension at least two. The genuine support
filtration and open-restriction immersion purity prove vanishing on every
analytic open. The actual supported stalk colimit therefore vanishes below
degree two, so the canonical global relative-to-sheaf map is invertible.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom.Cycles
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "E" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.structureMap) → ℂ)

local instance : Smooth X.structureMap := X.smooth

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace X.toOver ‹IsIntegral X.carrier› X.smooth

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold X.toOver ‹IsIntegral X.carrier› X.smooth ω

local instance _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referencePoints_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) := by
  let V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨X, inferInstance⟩
  exact inferInstanceAs (MetrizableSpace V.analyticSpace)

local instance : ChartedSpace E (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace (Over.mk X.structureMap) ‹IsIntegral X.carrier› X.smooth

local instance : IsManifold 𝓘(ℂ, E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) :=
  @ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold (Over.mk X.structureMap) ‹IsIntegral X.carrier› X.smooth ω

local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk X.structureMap)) := by
  change MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  infer_instance

/-- Each genuine smooth layer has vanishing support cohomology on every analytic open. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceLayer_open_cohomology_isZero
    (i : Fin L.referenceStratification.analyticSupportList.length)
    (U : Opens (TopCat.of (L.referenceStratification.analyticFiltrationComplement i)))
    (n : ℕ) (hn : n < 2) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ CycleClass.Geometric.ClosedSupportFiltration.Cycles.closedSupportLayer T
        (L.referenceStratification.analyticClosedFiltration i.castSucc)
        (L.referenceStratification.analyticClosedFiltration i.succ)}ᶜ n) := by
  let : MetrizableSpace (L.referenceStratification.analyticFiltrationComplement i) :=
    MetrizableSpace.subtype _
  have hdim : n < 2 * (Module.finrank ℂ E -
      Module.finrank ℂ (L.referenceStratification.analyticFiltrationPiece i).analyticModel) := by
    rw [Module.finrank_fin_fun, CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank,
      ← CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
    exact hn.trans_le (L.referenceLayer_realCodimension_ge_two i)
  have h := Open.ImmersionPurity.closedComplexImmersion_open_supportCohomology_isZero
    (L.referenceStratification.analyticFiltrationLayerInclusion i)
    (L.referenceStratification.isClosedEmbedding_analyticFiltrationLayerInclusion i)
    (L.referenceStratification.contMDiff_analyticFiltrationLayerInclusion i ω)
    (L.referenceStratification.mfderiv_analyticFiltrationLayerInclusion_injective i) U n hdim
  simp only [L.referenceStratification.range_analyticFiltrationLayerInclusion i] at h
  exact h

/-- The entire reference complement has low-degree vanishing on every analytic open. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceOpen_cohomology_isZero (U : Opens T) (n : ℕ) (hn : n < 2) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) U) n) := by
  let F : Fin (L.referenceStratification.analyticSupportList.length + 1) → Closeds T :=
    L.referenceStratification.analyticClosedFiltration
  have h := Open.SupportFiltration.closedSupportFiltration_open_isZero T U (ModuleCat.of ℚ ℚ)
    L.referenceStratification.analyticSupportList.length F
    L.referenceStratification.analyticClosedFiltration_monotone
    L.referenceStratification.analyticClosedFiltration_zero n
    (fun i V => L.referenceLayer_open_cohomology_isZero i V n hn)
  have hlast : (F (Fin.last L.referenceStratification.analyticSupportList.length) : Set T) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (L.referenceComplement : Set X.carrier) :=
    L.referenceStratification.analyticClosedFiltration_last
  have hA : {x : U | x.val ∈ (F
        (Fin.last L.referenceStratification.analyticSupportList.length) : Set T)}ᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) U := by
    ext x
    rw [hlast]
    change (¬¬ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ L.rationalReferenceOpen) ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ L.rationalReferenceOpen
    exact not_not
  rwa [hA] at h

/-- Low-degree supported stalk vanishing follows from the actual neighborhood colimit. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceSupportedStalk_isZero (x : T) (n : ℕ) (hn : n < 2) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex L.rationalSectionSupportComplex x).homology n) := by
  let F := AlgebraicTopology.Cohomology.Singular.RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of ℚ ℚ) T
    (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) x n
  have hF : IsZero F := F.isZero (fun U => L.referenceOpen_cohomology_isZero U.unop.1 n hn)
  exact ((colimit.isColimit F).isZero_pt hF).of_iso
    (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso ℚ T (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) x n)

/-- The actual canonical relative-to-sheaf map is invertible in degree two. -/
instance _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceGlobalSectionMap_isIso : IsIso
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) 2) :=
  CycleClass.Geometric.ComplexThom.Cycles.relativeCohomologyGlobalSectionMap_isIso T (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) 2
    L.referenceSupportedStalk_isZero

/-- The actual rational-section section lifts to genuine relative singular cohomology. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionSupportedClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) 2 :=
  (asIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T
    (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) 2)).inv L.rationalSectionSupportedSection

/-- The lifted relative class has precisely the constructed supported section. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionSupportedClass_section :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) 2
      L.rationalSectionSupportedClass = L.rationalSectionSupportedSection :=
  (asIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T
    (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) 2)).inv_hom_id_apply _

/-- On each actual algebraic chart, the global relative class has the constructed local image. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionSupportedClass_localImage (i : X.carrier) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen)
      (L.analyticCover i) 2
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T
        (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) (L.analyticCover i) 2
        L.rationalSectionSupportedClass) =
      L.rationalSectionLocalSection i (L.trivializingOpen i) le_rfl := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) (L.analyticCover i) 2) L.rationalSectionSupportedClass
  change (L.rationalSectionSupportComplex.homology 2).obj.map
      (homOfLE (le_top : L.analyticCover i ≤ ⊤)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T
        (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen) 2 L.rationalSectionSupportedClass) = _ at h
  rw [L.rationalSectionSupportedClass_section, L.rationalSectionSupportedSection_restrict] at h
  exact h.symm

/-- Forget support to obtain the absolute singular class of the actual section's local winding. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionAbsoluteWindingClass : X.rationalCohomology 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T (Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T) 2
    L.rationalSectionSupportedClass

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ReferencePurity
