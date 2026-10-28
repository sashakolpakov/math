import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.ChernRestriction
import OAI.AlgebraicGeometry.DivisorClass.Chern.ReferencePurity

/-! # Winding Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparison

noncomputable section

/-!
# ChernClass: first Chern class and the global winding of the actual rational section

The constructed relative Chern class and the previously glued relative
winding class have identical supported-sheaf images on the actual logarithmic
cover. Proved reference-complement purity makes the canonical global section
map injective, identifying the two genuine relative singular classes.

The separate comparison with the multiplicity-weighted geometric divisor
class is not asserted here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

/-- Restrict the original supported winding section to any analytic open inside an algebraic frame. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionSupportedSection_restrictOn (i : X.carrier) (U : Opens T)
    (hi : U ≤ L.analyticCover i) :
    ((L.rationalSectionSupportComplex.homology 2).obj).map (homOfLE (le_top : U ≤ ⊤)).op L.rationalSectionSupportedSection =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U 2
        (Supported.Winding.supportedWindingClass (TopCat.of U) (L.analyticReferenceLocus U)
          (L.referenceEquationOn i U hi) (L.referenceEquationOn_ne_zero i U hi)) := by
  let f : TopCat.of U ⟶ TopCat.of (L.analyticCover i) :=
    TopCat.ofHom (LogRefinementOpen.Construction.openInclusionMap hi)
  have hr : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (A := L.analyticReferenceLocus U) (B := L.referenceLocus (L.trivializingOpen i))
      (fun _ hx => hx) 2 (L.rationalSectionLocalSupportedClass i (L.trivializingOpen i) le_rfl) =
    Supported.Winding.supportedWindingClass (TopCat.of U) (L.analyticReferenceLocus U)
      (L.referenceEquationOn i U hi) (L.referenceEquationOn_ne_zero i U hi) := by
    unfold Line.Bundles.AlgebraicLineBundle.rationalSectionLocalSupportedClass
    rw [Supported.Winding.supportedWindingClass_pullback]
    apply Supported.Winding.supportedWindingClass_congr
    apply ContinuousMap.ext
    intro p
    rfl
  have hn := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_naturality (ModuleCat.of ℚ ℚ) T O (homOfLE hi) 2)
    (L.rationalSectionLocalSupportedClass i (L.trivializingOpen i) le_rfl)
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (A := L.analyticReferenceLocus U) (B := L.referenceLocus (L.trivializingOpen i))
        (fun _ hx => hx) 2 (L.rationalSectionLocalSupportedClass i (L.trivializingOpen i) le_rfl)) =
    ((L.rationalSectionSupportComplex.homology 2).obj).map (homOfLE hi).op (L.rationalSectionLocalSection i (L.trivializingOpen i) le_rfl) at hn
  rw [hr] at hn
  calc
    _ = ((L.rationalSectionSupportComplex.homology 2).obj).map (homOfLE hi).op
        (((L.rationalSectionSupportComplex.homology 2).obj).map (homOfLE (le_top : L.analyticCover i ≤ ⊤)).op L.rationalSectionSupportedSection) := by
      rw [← ConcreteCategory.comp_apply, ← ((L.rationalSectionSupportComplex.homology 2).obj).map_comp]
      rfl
    _ = _ := by rw [L.rationalSectionSupportedSection_restrict]; exact hn.symm

/-- The two independently constructed genuine relative classes have identical local images. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_eq_supported :
    L.rationalSectionChernRelativeClass = L.rationalSectionSupportedClass := by
  have := L.referenceGlobalSectionMap_isIso
  apply (ModuleCat.mono_iff_injective
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2)).mp inferInstance
  rw [L.rationalSectionSupportedClass_section]
  let V : (Fin 1 → L.LogCoverIndex) → Opens T := fun a => AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a
  have hV : (⊤ : Opens T) ≤ iSup V := by
    intro p _
    obtain ⟨i, hi⟩ := L.logCover_covers p
    apply Opens.mem_iSup.mpr
    refine ⟨fun _ => i, ?_⟩
    exact (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection L.logCover (fun _ : Fin 1 => i) p).mpr (fun _ => hi)
  apply (L.rationalSectionSupportComplex.homology 2).eq_of_locally_eq' V ⊤
    (fun _ => homOfLE le_top) hV
  intro a
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) 2) L.rationalSectionChernRelativeClass
  change ((L.rationalSectionSupportComplex.homology 2).obj).map (homOfLE (le_top : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a ≤ ⊤)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 L.rationalSectionChernRelativeClass) =
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) 2
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) 2 L.rationalSectionChernRelativeClass) at h
  rw [L.rationalSectionChernRelativeClass_local] at h
  exact h.trans (L.rationalSectionSupportedSection_restrictOn (L.logParent (a 0))
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a)
    ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a 0).trans (L.logCover_subset (a 0)))).symm

/-- The actual first Chern class is the absolute image of the previously
constructed global winding class of the same algebraic rational section. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_rationalSectionAbsoluteWindingClass :
    First.firstChernClassQ X L = L.rationalSectionAbsoluteWindingClass := by
  rw [← L.rationalSectionChernRelativeClass_absolute, L.rationalSectionChernRelativeClass_eq_supported]
  rfl

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparison
