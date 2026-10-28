import OAI.AlgebraicGeometry.ComplexMultiplication.IntegerSingularHomology
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeUnitClass
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension

/-! # Relative Absolute Class -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeAbsoluteClass

noncomputable section

/-! # Forgetting the actual relative unit gives the canonical ordinary class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ)
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local instance CMOriginalRelativeRawAbsoluteClass.localInstance1 : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X

/-- The literal relative inclusion, with only the original complex-degree isomorphisms. -/
def originalRelativeRawAbsoluteClass
    (a : (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).X₁.homology (n : ℤ)) :
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ (Y)).homology n :=
  ((AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ (Y)).extendHomologyIso
    ComplexShape.embeddingUpNat rfl).hom
      (homologyMap (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual ℚ (Y) ⊤).inv (n : ℤ)
        (homologyMap (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).f (n : ℤ) a))

omit [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
theorem originalRelativeRawAbsoluteClass_normalization
    (a : (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).X₁.homology (n : ℤ)) :
    (Coefficient.SheafComparison.rawSingularHomologyIso ℚ (Y) n).hom (originalRelativeRawAbsoluteClass X S n a) =
    AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ n (Opens.inclusionTopIso (Y)).inv
      (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute ℚ
        (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) S) n
        (RelativeUnitClass.originalOpenRelativeClass X S n a)) := by
  let P := AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair (Y) (Opens.infLELeft ⊤ S.compl)
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let f := (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ P).f
  have hf := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.up ℤ)
      (n : ℤ)).map f) F
  have hfa := ConcreteCategory.congr_hom hf a
  dsimp only [originalRelativeRawAbsoluteClass]
  rw [IntegerSingularHomology.rawIntegerSingularHomology_normalization]
  change homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen ℚ (Y)).inv n
    (((AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex ℚ (TopCat.of (⊤ : Opens (Y)))).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom
      ((((AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ P).X₂.sc (n : ℤ)).mapHomologyIso F).hom
        (homologyMap ((F.mapHomologicalComplex ℤᵘᵖ).map f) (n : ℤ) a))) = _
  rw [show (((AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ P).X₂.sc (n : ℤ)).mapHomologyIso F).hom
      (homologyMap ((F.mapHomologicalComplex ℤᵘᵖ).map f) (n : ℤ) a) =
      homologyMap f (n : ℤ)
        ((((AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ P).X₁.sc (n : ℤ)).mapHomologyIso F).hom a)
    from hfa]
  have hr := RelativeDualAbsoluteExtension.relativeDualAbsoluteExtension ℚ P n
    ((((AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ P).X₁.sc (n : ℤ)).mapHomologyIso F).hom a)
  have hrt := congrArg (fun b => HomologicalComplex.homologyMap
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen ℚ (Y)).inv n b) hr.symm
  refine hrt.trans ?_

  let b := AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ P n
    ((((AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ P).X₁.sc (n : ℤ)).mapHomologyIso F).hom a)
  have hn := RelativeDualAbsoluteExtension.relativeToAbsolute_naturality ℚ
    (AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement (Y) S S.isClosed ⊤).inv n b
  change AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute ℚ
    (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) S) n
      (RelativeUnitClass.originalOpenRelativeClass X S n a) =
    AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ n (𝟙 (TopCat.of (⊤ : Opens (Y))))
      (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute ℚ P n b) at hn
  rw [AlgebraicTopology.Singular.CohomologyTo.cohomologyMap_id, LinearMap.id_apply] at hn
  exact congrArg (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ n (Opens.inclusionTopIso (Y)).inv) hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeAbsoluteClass
