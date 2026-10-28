import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleLowestNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.AdditiveIsoSquare

/-! # Injective Relative Open Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveRelativeOpenNaturality

noncomputable section

section

/-! # The genuine injective-relative comparison commutes with open restriction -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf _root_.HomologicalComplex

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))
  {V W : Opens (ComplexPoint.Basic.ComplexSchemePoint X)} (a : W ⟶ V) (n : ℕ)

theorem injectiveSingularOpenIso_naturality :
    homologyMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ
      (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl) a)
      (n : ℤ) ≫
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl W (n : ℤ)).hom =
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).hom ≫
      homologyMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S) a) (n : ℤ) := by
  let : ∀ U : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace U := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  let K := AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
  let L := ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S
  let f := ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X S.compl
  have hn := ((AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportEvaluationRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) a).mapHomologicalComplex
    ℤᵘᵖ).naturality f
  have hk : AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ K a ≫
      ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) W).mapHomologicalComplex ℤᵘᵖ).map f =
    ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex ℤᵘᵖ).map f ≫
      AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ L a := hn.symm
  change HomologicalComplex.homologyMap _ (n : ℤ) ≫ HomologicalComplex.homologyMap _ (n : ℤ) =
    HomologicalComplex.homologyMap _ (n : ℤ) ≫ HomologicalComplex.homologyMap _ (n : ℤ)
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ)) hk

theorem injectiveRelativeOpen_naturality
    (z : ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S))).homology (n : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S W n
      (homologyMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S) a) (n : ℤ) z) =
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
      (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap (W := (W : Set (ComplexPoint.Basic.ComplexSchemePoint X)))
        (V := (V : Set (ComplexPoint.Basic.ComplexSchemePoint X))) (leOfHom a) S)
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S V n z) := by
  let : ∀ U : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace U := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  let K := AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
  let L := ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S
  let eV := ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)
  let eW := ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl W (n : ℤ)
  let rK := homologyMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ K a) (n : ℤ)
  let rL := homologyMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ L a) (n : ℤ)
  have h : rK ≫ eW.hom = eV.hom ≫ rL := injectiveSingularOpenIso_naturality X S a n
  have hi : eW.inv (rL z) = rK (eV.inv z) := by
    exact AdditiveIsoSquare.additiveIsoSquare_inv_apply eV eW rK rL h z
  change AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed W n (eW.inv (rL z)) = _
  rw [hi]
  exact AlgebraicTopology.Support.SingularSectionNaturality.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed a n (eV.inv z)

end

/-! # The original supported resolution takes the genuine global relative cycle class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf _root_.HomologicalComplex

theorem transportedHomologyMap {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) {i j : ℤ} (h : i = j)
    {FC : C → Type*} {CC : C → C → Type*} [∀ A B, FunLike (CC A B) (FC A) (FC B)]
    [ConcreteCategory C CC] (z : FC (K.homology j)) :
    h ▸ homologyMap f i (h.symm ▸ z) = homologyMap f j z := by
  cases h
  rfl

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) (p : ℕ)

/-- The same supported cohomology, with the proved equality of integer degree spellings. -/
def originalCycleSupportedDegreeClass
    (z : ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)))).homology ((2 * p : ℕ) : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  show ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex
    ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)))).homology (2 * (p : ℤ)) from
    he ▸ z

theorem originalCycleSmoothRelativeClass_degreeCast (hx : Order.coheight x = p)
    (z : ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)))).homology ((2 * p : ℕ) : ℤ)) :
    Reference.CycleLowestNormalization.originalCycleSmoothRelativeClass X x hx (originalCycleSupportedDegreeClass X x p z) =
    ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x) (2 * p)
      (homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) ((2 * p : ℕ) : ℤ) z) := by
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  have hc := transportedHomologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) he z
  unfold Reference.CycleLowestNormalization.originalCycleSmoothRelativeClass originalCycleSupportedDegreeClass
  change ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x) (2 * p)
    (he ▸ homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ))
      (he.symm ▸ z)) = _
  exact congrArg (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (2 * p)) hc

/-- The inverse of the original relative/injective comparison, with the proved degree equality. -/
def originalCycleRelativeToSupportedInjectiveClass
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (Cycle.Support.cycleComponentSupport X x)) (2 * p)) :
    ComplexPoint.Basic.ComplexSchemePoint.CycleComponentSupportedCohomology X x p :=
  originalCycleSupportedDegreeClass X x p
    ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) ⊤ (2 * p)).symm a)

theorem originalCycleSmoothRelativeClass_fromRelativeClass (hx : Order.coheight x = p)
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (Cycle.Support.cycleComponentSupport X x)) (2 * p)) :
    Reference.CycleLowestNormalization.originalCycleSmoothRelativeClass X x hx
      (originalCycleRelativeToSupportedInjectiveClass X x p a) =
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
      (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap
        (Set.subset_univ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x : Set (ComplexPoint.Basic.ComplexSchemePoint X)))
        (Cycle.Support.cycleComponentSupport X x)) a := by
  let z := (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) ⊤ (2 * p)).symm a
  let e := ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x) (2 * p)
  have hd : Reference.CycleLowestNormalization.originalCycleSmoothRelativeClass X x hx
      (originalCycleRelativeToSupportedInjectiveClass X x p a) =
    e (homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) ((2 * p : ℕ) : ℤ) z) := by
    exact originalCycleSmoothRelativeClass_degreeCast X x p hx z
  have h := injectiveRelativeOpen_naturality X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x)
    (V := ⊤) (W := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
    (homOfLE le_top) (2 * p)
    ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x) ⊤ (2 * p)).symm a)
  rw [AddEquiv.apply_symm_apply] at h
  exact hd.trans h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveRelativeOpenNaturality
