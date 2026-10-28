import OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoRemoval
import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations

/-! # Codimension One Detection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionOneDetection

noncomputable section

/-!
# ChernClass: codimension-one neighborhoods determine the global relative class

Any algebraic neighborhood of each codimension-one scheme point suffices.
Their union with the reference open misses only a closed codimension-two
subset. Actual purity and the canonical sheaf comparisons prove detection;
no descent property of an unproved cohomology presheaf is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

/-- Actual restrictions on a neighborhood of each codimension-one point
determine a genuine global relative class supported outside the reference open. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeClass_eq_of_codimensionOne_restrictions
    (U : {z : X.carrier // Order.coheight z = 1} → X.carrier.Opens)
    (hU : ∀ z, z.val ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
    (hab : ∀ z, CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 b) : a = b := by
  let R := L.rationalReferenceOpen ⊔ iSup U
  let F := R.compl
  let G : Opens T := Line.Bundles.AlgebraicLineBundle.analyticOpen X R
  let S := (L.rationalSectionSupportComplex.homology 2).obj
  let : Nonempty L.rationalReferenceOpen := ⟨⟨genericPoint X.carrier, L.mem_trivializingOpen _⟩⟩
  have hF : ∀ z ∈ F, 1 < Order.coheight z :=
    CodimensionTwoRemoval.Construction.complement_comparisonOpen_coheight X L.rationalReferenceOpen U hU
  have hO : (O : Set T) ⊆ Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl := by
    change (O : Set T) ⊆ Line.Bundles.AlgebraicLineBundle.analyticOpen X R.compl.compl
    rw [Opens.compl_compl]
    exact fun _ hx => Or.inl hx
  have hi := CodimensionTwoRemoval.Construction.codimensionTwo_relativeRestriction_isIso X F hF (O : Set T) hO
  have hiG : IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G 2) := by
    change IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X R.compl.compl) 2) at hi
    rw [Opens.compl_compl] at hi
    exact hi
  apply (ModuleCat.mono_iff_injective
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G 2)).mp inferInstance
  apply (ModuleCat.mono_iff_injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O G 2)).mp inferInstance
  have image (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
      (V : Opens T) :
      S.map (homOfLE (le_top : V ≤ ⊤)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 c) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V 2
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) V 2 c) :=
    ConcreteCategory.congr_hom
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O V 2) c
  rw [← image a G, ← image b G]
  apply CycleClass.Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O G 2
  intro x hxG hxO
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ iSup U := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ L.rationalReferenceOpen ⊔ iSup U at hxG
    exact hxG.resolve_left hxO
  obtain ⟨z, hz⟩ := Opens.mem_iSup.mp hx
  have hz' : x ∈ Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z) := hz
  have he : S.map (homOfLE (le_top : Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z) ≤ ⊤)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 a) =
      S.map (homOfLE (le_top : Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z) ≤ ⊤)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 b) := by
    rw [image a, image b, hab z]
  have hg := congrArg (TopCat.Presheaf.germ S (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) x hz') he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact hg

/-- The actual Chern lift is characterized by the original section
equations on any chosen algebraic frame neighborhoods of codimension one. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_unique_codimensionOne
    (U : {z : X.carrier // Order.coheight z = 1} → X.carrier.Opens)
    (hU : ∀ z, z.val ∈ U z)
    (i : {z : X.carrier // Order.coheight z = 1} → X.carrier)
    (hUi : ∀ z, U z ≤ L.trivializingOpen (i z))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
    (ha : ∀ z, CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a = L.rationalSectionLocalSupportedClass (i z) (U z) (hUi z)) :
    a = L.rationalSectionChernRelativeClass := by
  apply L.relativeClass_eq_of_codimensionOne_restrictions U hU a L.rationalSectionChernRelativeClass
  intro z
  exact (ha z).trans (L.rationalSectionChernRelativeClass_algebraic (i z) (U z) (hUi z)).symm

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionOneDetection
