/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality
import OAI.AlgebraicTopology.Support.SingularSectionCohomology
import OAI.AlgebraicTopology.Singular.CochainOpenConeNaturality
import OAI.AlgebraicTopology.Support.RelativeCohomologyEq

/-! # Singular Section Naturality -/

namespace OAI.AlgebraicTopology.Support.SingularSectionNaturality.Singular

noncomputable section

/-! # Naturality of supported singular-section relative cohomology -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open _root_.TopCat.Sheaf

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (U : Opens X) {V W : Opens X} (a : W ⟶ V)

/-- Let `X` be Hausdorff with every open subset paracompact, and let `U,V ⊆ X` be open. Write `C^•`
for sheafified rational singular cochains. This identifies `H^n(Γ(V, Γ_{X \ U}(C^•)))` with
`H^{n-1}(Cone(C^•(V) → C^•(V ∩ U)))`, using the inclusion of the kernel of restriction and
extension to integer degrees. -/
def supportedSingularSectionConeHomologyIso (V : Opens X) (n : ℤ) :
    ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology n ≅
        (Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U)).homology (n - 1) :=
  SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V (SingularFlasqueModel.Singular.rationalSingularCochainComplex X)
    (fun _ => inferInstance) n ≪≫
  HomologicalComplex.homologyMapIso (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X
    (Singular.SheafCochain.singularCochainSheafComplex ℚ X) (Opens.infLELeft V U)) (n - 1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported kernel-to-singular-cone comparison respects open restriction. -/
@[reassoc]
lemma supportedSingularSectionConeHomologyIso_naturality (n : ℤ) :
    HomologicalComplex.homologyMap
      (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a) n ≫
      (supportedSingularSectionConeHomologyIso X U W n).hom =
    (supportedSingularSectionConeHomologyIso X U V n).hom ≫
      HomologicalComplex.homologyMap
        (Singular.CochainOpenConeNaturality.openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft W U)
          a (homOfLE (inf_le_inf_right U (leOfHom a)))) (n - 1) := by
  dsimp only [supportedSingularSectionConeHomologyIso, Iso.trans_hom]
  change HomologicalComplex.homologyMap
      (SectionRestrictionConeNaturality.TopCat.Sheaf.supportRestrictionSectionsComplexMap X U (SingularFlasqueModel.Singular.rationalSingularCochainComplex X) a).τ₁ n ≫
      ((SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U W (SingularFlasqueModel.Singular.rationalSingularCochainComplex X)
        (fun _ => inferInstance) n).hom ≫ _) = _
  rw [SectionRestrictionConeNaturality.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone_naturality_assoc X U
    (SingularFlasqueModel.Singular.rationalSingularCochainComplex X) a]
  simp only [Category.assoc]
  congr 1
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ (n - 1)
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (SectionRestrictionConeNaturality.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso_naturality X
    (Singular.SheafCochain.singularCochainSheafComplex ℚ X) (Opens.infLELeft V U) (Opens.infLELeft W U)
    a (homOfLE (inf_le_inf_right U (leOfHom a))))

/-- Restriction naturality of the whole supported-section-to-relative equivalence. -/
lemma supportedRationalSingularSectionCohomologyEquivRelative_naturality
    (n : ℕ)
    (z : ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology (n : ℤ)) :
    SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X U W n
      (HomologicalComplex.homologyMap
        (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a)
          (n : ℤ) z) =
    Singular.Cohomology.relativeCohomologyMap ℚ n
      (Singular.CochainOpenConeNaturality.openInclusionPairMap X (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a))))
      (SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X U V n z) := by
  change Singular.SheafCochainOpenCone.openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft W U) n
      ((supportedSingularSectionConeHomologyIso X U W (n : ℤ)).hom
        (HomologicalComplex.homologyMap
          (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a)
            (n : ℤ) z)) = _
  have h := congrArg (fun f => f z)
    (supportedSingularSectionConeHomologyIso_naturality X U a (n : ℤ))
  change (supportedSingularSectionConeHomologyIso X U W (n : ℤ)).hom
      (HomologicalComplex.homologyMap
        (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U) a)
          (n : ℤ) z) =
    HomologicalComplex.homologyMap
      (Singular.CochainOpenConeNaturality.openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a)))) ((n : ℤ) - 1)
      ((supportedSingularSectionConeHomologyIso X U V (n : ℤ)).hom z) at h
  rw [h]
  exact Singular.CochainOpenConeNaturality.openSingularSheafRestrictionConeCohomologyEquivRelative_naturality X
    (Opens.infLELeft V U) (Opens.infLELeft W U) a
    (homOfLE (inf_le_inf_right U (leOfHom a))) n _

/-- The final support-complement comparison preserves ambient-open restrictions. -/
lemma supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
    (S : Set X) (hS : IsClosed S) {V W : Opens X} (a : W ⟶ V) (n : ℕ)
    (z : ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS W n
      (HomologicalComplex.homologyMap
        (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
          (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) a) (n : ℤ) z) =
    Singular.Cohomology.relativeCohomologyMap ℚ n
      (LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap
        (W := (W : Set X)) (V := (V : Set X)) (leOfHom a) S)
      (SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n z) := by
  change Singular.Cohomology.relativeCohomologyMap ℚ n (SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement X S hS W).inv
      (SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X _ W n _) =
    Singular.Cohomology.relativeCohomologyMap ℚ n _
      (Singular.Cohomology.relativeCohomologyMap ℚ n (SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement X S hS V).inv
        (SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative X _ V n z))
  rw [supportedRationalSingularSectionCohomologyEquivRelative_naturality,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Singular.CohomologyTo.relativeCohomologyMap_comp,
    ← Singular.CohomologyTo.relativeCohomologyMap_comp]
  congr 2

end

end OAI.AlgebraicTopology.Support.SingularSectionNaturality.Singular
