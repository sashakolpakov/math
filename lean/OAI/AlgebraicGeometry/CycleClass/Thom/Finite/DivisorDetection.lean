import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComplementPurity
import OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionTwoRemoval
import OAI.AlgebraicGeometry.DivisorClass.Chern.Support

/-! # Divisor Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.DivisorDetection

noncomputable section

/-! Actual relative degree-two classes supported outside any nonempty
algebraic open are detected on the finitely many missing codimension-one points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComplementPurity.Constructions
variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (R : X.carrier.Opens) [Nonempty R]
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R

/-- Actual restrictions on a neighborhood of each codimension-one point
determine a genuine global relative class supported outside the reference open. -/
theorem relativeClass_eq_of_codimensionOne_restrictions
    (U : {z : X.carrier // Order.coheight z = 1} → X.carrier.Opens)
    (hU : ∀ z, z.val ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
    (hab : ∀ z, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 b) : a = b := by
  let GAlg := R ⊔ iSup U
  let F := GAlg.compl
  let G : Opens T := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X GAlg
  let S := ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O).homology 2).obj
  have hF : ∀ z ∈ F, 1 < Order.coheight z :=
    DivisorClass.Chern.CodimensionTwoRemoval.Construction.complement_comparisonOpen_coheight X R U hU
  have hO : (O : Set T) ⊆ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X F.compl := by
    change (O : Set T) ⊆ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X GAlg.compl.compl
    rw [Opens.compl_compl]
    exact fun _ hx => Or.inl hx
  have hi := DivisorClass.Chern.CodimensionTwoRemoval.Construction.codimensionTwo_relativeRestriction_isIso X F hF (O : Set T) hO
  have hiG : IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G 2) := by
    change IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X GAlg.compl.compl) 2) at hi
    rw [Opens.compl_compl] at hi
    exact hi
  apply (ModuleCat.mono_iff_injective
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G 2)).mp inferInstance
  apply (ModuleCat.mono_iff_injective (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O G 2)).mp inferInstance
  have image (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
      (V : Opens T) :
      S.map (homOfLE (le_top : V ≤ ⊤)).op
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 c) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V 2
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) V 2 c) :=
    ConcreteCategory.congr_hom
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O V 2) c
  rw [← image a G, ← image b G]
  apply Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O G 2
  intro x hxG hxO
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ iSup U := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ R ⊔ iSup U at hxG
    exact hxG.resolve_left hxO
  obtain ⟨z, hz⟩ := Opens.mem_iSup.mp hx
  have hz' : x ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z) := hz
  have he : S.map (homOfLE (le_top : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z) ≤ ⊤)).op
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 a) =
      S.map (homOfLE (le_top : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z) ≤ ⊤)).op
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O 2 b) := by
    rw [image a, image b, hab z]
  have hg := congrArg (TopCat.Presheaf.germ S (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) x hz') he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact hg

/-- The actual codimension-one points outside the chosen reference open. -/
abbrev ComplementDivisorPoint :=
  {z : X.carrier // Order.coheight z = 1 ∧ z ∉ R}

instance complementDivisorPoint_finite : Finite (ComplementDivisorPoint X R) := by
  exact (DivisorClass.Chern.Support.Construction.finite_codimension_one_complement X.carrier R).to_subtype

/-- Every original relative class restricts to zero on the reference open. -/
theorem relativeClass_reference_restriction_zero
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) O 2 a = 0 := by
  apply (ModuleCat.mono_iff_injective (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O O 2)).mp inferInstance
  apply Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O O 2
  intro x hx hnot
  exact (hnot hx).elim

/-- Actual relative classes are determined by finitely many algebraic
neighborhood restrictions, one at each reference divisor point. -/
theorem relativeClass_eq_of_finite_divisor_restrictions
    (U : ComplementDivisorPoint X R → X.carrier.Opens) (hU : ∀ z, z.val ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
    (hab : ∀ z, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 b) : a = b := by
  classical
  let V (z : {z : X.carrier // Order.coheight z = 1}) : X.carrier.Opens :=
    if hz : z.val ∈ R then R
    else U ⟨z.val, z.property, hz⟩
  have hV (z : {z : X.carrier // Order.coheight z = 1}) : z.val ∈ V z := by
    dsimp only [V]
    split_ifs with hz
    · exact hz
    · exact hU ⟨z.val, z.property, hz⟩
  apply relativeClass_eq_of_codimensionOne_restrictions X R V hV a b
  intro z
  by_cases hz : z.val ∈ R
  · have he : V z = R := dite_eq_left hz
    rw [he, relativeClass_reference_restriction_zero X R a, relativeClass_reference_restriction_zero X R b]
  · have he : V z = U ⟨z.val, z.property, hz⟩ := dite_eq_right hz
    rw [he]
    exact hab ⟨z.val, z.property, hz⟩

/-- The finite family of actual restrictions is injective. -/
theorem finite_divisor_restriction_injective
    (U : ComplementDivisorPoint X R → X.carrier.Opens) (hU : ∀ z, z.val ∈ U z) :
    Function.Injective (fun a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 =>
      fun z : ComplementDivisorPoint X R =>
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
          (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a) := by
  intro a b hab
  exact relativeClass_eq_of_finite_divisor_restrictions X R U hU a b (congrFun hab)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.DivisorDetection
