import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections

/-! # Support Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection

noncomputable section

section

/-! Neighborhoods of all components in the minimum codimension retain
the actual supported cohomology in its first possible degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Neighborhoods

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] (F : Closeds X.left) (c : ℕ)

/-- Actual irreducible supports in the first possible codimension. -/
abbrev MinimalSupport :=
  {Z : IrreducibleCloseds X.left // (Z : Set X.left) ⊆ F ∧
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom}

variable (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : MinimalSupport X F c → X.left.Opens)
  (hU : ∀ Z, irreducibleSetEquivPoints Z.val ∈ U Z)

include hc hU in
omit [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] in
theorem omittedSupport_dimension (Z : IrreducibleCloseds X.left)
    (hZ : (Z : Set X.left) ⊆ (F.compl ⊔ iSup U).compl) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + (c + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  have hZF : (Z : Set X.left) ⊆ F := by
    intro x hx
    by_contra hxF
    exact hZ hx (Or.inl hxF)
  have hd := hc Z hZF
  by_contra hn
  have he : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by omega
  let T : MinimalSupport X F c := ⟨Z, hZF, he⟩
  have hz : irreducibleSetEquivPoints Z ∈ (Z : Set X.left) :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  exact hZ hz (Or.inr (Opens.mem_iSup.mpr ⟨T, hU T⟩))

variable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

include hc hU in
theorem comparisonOpen_relativeRestriction_isIso :
    IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T
      (SectionEvaluation.Constructions.analyticOpen X F.compl : Set T) (SectionEvaluation.Constructions.analyticOpen X (F.compl ⊔ iSup U)) (2 * c)) := by
  let G := F.compl ⊔ iSup U
  have hG := omittedSupport_dimension X F c hc U hU
  have hv (n : ℕ) (hn : n < 2 * (c + 1)) :
      IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T
        (SectionEvaluation.Constructions.analyticOpen X G : Set T) n) := by
    have h := ClosedSupportPurity.Constructions.closedSupport_cohomology_isZero X G.compl
      (c + 1) hG n hn
    rw [Opens.compl_compl] at h
    exact h
  exact Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction_isIso (ModuleCat.of ℚ ℚ) T
    (SectionEvaluation.Constructions.analyticOpen X G : Set T) (SectionEvaluation.Constructions.analyticOpen X F.compl : Set T)
    (fun _ hx => Or.inl hx) (2 * c) (hv (2 * c) (by omega)) (hv (2 * c + 1) (by omega))

end Constructions.Neighborhoods

end

/-! Supported classes in the first possible degree are detected on actual
algebraic neighborhoods of the minimum-codimension support components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Neighborhoods.MinimalSupport X F c → X.left.Opens)
  (hU : ∀ Z, irreducibleSetEquivPoints Z.val ∈ U Z)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl

include hc hU in
theorem relativeClass_eq_of_component_neighborhoods
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c))
    (hab : ∀ Z, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (SectionEvaluation.Constructions.analyticOpen X (U Z)) (2 * c) a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (SectionEvaluation.Constructions.analyticOpen X (U Z)) (2 * c) b) : a = b := by
  let G : Opens T := SectionEvaluation.Constructions.analyticOpen X (F.compl ⊔ iSup U)
  let S := ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O).homology (2 * c)).obj
  have hi : IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G (2 * c)) :=
    Neighborhoods.comparisonOpen_relativeRestriction_isIso X F c hc U hU
  have hs : IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O G (2 * c)) :=
    ClosedSupportSections.Constructions.closedSupportSectionMap_isIso X F c hc G
  apply (ModuleCat.mono_iff_injective
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G (2 * c))).mp inferInstance
  apply (ModuleCat.mono_iff_injective
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O G (2 * c))).mp inferInstance
  have image (a' : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c))
      (V : Opens T) :
      S.map (homOfLE (le_top : V ≤ ⊤)).op
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) a') =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V (2 * c)
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) V (2 * c) a') :=
    ConcreteCategory.congr_hom
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O V (2 * c)) a'
  rw [← image a G, ← image b G]
  apply Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O G (2 * c)
  intro x hxG hxO
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ iSup U := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ F.compl ⊔ iSup U at hxG
    exact hxG.resolve_left hxO
  obtain ⟨Z, hZ⟩ := Opens.mem_iSup.mp hx
  have hz' : x ∈ SectionEvaluation.Constructions.analyticOpen X (U Z) := hZ
  have he : S.map (homOfLE (le_top : SectionEvaluation.Constructions.analyticOpen X (U Z) ≤ ⊤)).op
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) a) =
      S.map (homOfLE (le_top : SectionEvaluation.Constructions.analyticOpen X (U Z) ≤ ⊤)).op
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) b) := by
    rw [image a, image b, hab Z]
  have hg := congrArg (TopCat.Presheaf.germ S (SectionEvaluation.Constructions.analyticOpen X (U Z)) x hz') he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact hg

include hc hU in
theorem component_neighborhood_restriction_injective :
    Function.Injective (fun a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c) =>
      fun Z : Neighborhoods.MinimalSupport X F c =>
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
          (SectionEvaluation.Constructions.analyticOpen X (U Z)) (2 * c) a) := by
  intro a b hab
  exact relativeClass_eq_of_component_neighborhoods X F c hc U hU a b (congrFun hab)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection
