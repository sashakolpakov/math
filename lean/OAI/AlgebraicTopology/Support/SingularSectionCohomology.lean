/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.SectionRestrictionIs
import OAI.AlgebraicTopology.Support.SingularFlasqueOn
import OAI.AlgebraicTopology.Singular.SheafCochainOpenCone
import OAI.AlgebraicTopology.LocalHomology.FlattenedSupport

/-! # Singular Section Cohomology -/

namespace OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular

noncomputable section

/-!
# Supported singular-section cohomology on arbitrary opens

The kernel of restriction on singular cochain sheaves is compared to the relative singular
pair on an arbitrary open neighborhood. The construction composes the flasque kernel/cone
comparison, the canonical grading comparison, and the sheafification-unit cone comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : TopCat.{0})

/-- Let `X` be a topological space, `S ⊆ X` closed, and `V ⊆ X` open. This homeomorphism identifies
the subspace `V ∩ (X \ S)` of `X` with the subspace `{v ∈ V | v ∉ S}` of `V`; it leaves each
underlying point unchanged. -/
def openIntersectionSupportComplementHomeomorph (S : Set X) (hS : IsClosed S) (V : Opens X) :
    ↥(V ⊓ (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X)) ≃ₜ {v : V | v.1 ∉ S} where
  toEquiv := (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ V) (· ∉ S)).symm
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Let `X` be a topological space, `S ⊆ X` closed, and `V ⊆ X` open. This identifies the pairs `(V,
V ∩ (X \ S))` and `(V, V \ S)`, acting as the identity on underlying points in both spaces. -/
def openIntersectionPairIsoSupportComplement (S : Set X) (hS : IsClosed S) (V : Opens X) :
    Singular.SheafCochainOpenCone.openInclusionPair X (Opens.infLELeft V (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X)) ≅
      LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (V : Set X) S where
  hom := TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨openIntersectionSupportComplementHomeomorph X S hS V,
      (openIntersectionSupportComplementHomeomorph X S hS V).continuous⟩) rfl
  inv := TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨(openIntersectionSupportComplementHomeomorph X S hS V).symm,
      (openIntersectionSupportComplementHomeomorph X S hS V).symm.continuous⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V] (U V : Opens X)

/-- Let `X` be a Hausdorff topological space whose every open subset is paracompact. Let `U` and `V`
be open and `C^•` the complex of sheafified rational singular cochains. The sections on `V` that
vanish on `V ∩ U` form a subcomplex. This additive equivalence identifies its degree-`n`
cohomology with relative singular cohomology `H^n(V, V ∩ U; ℚ)`. -/
def supportedRationalSingularSectionCohomologyEquivRelative (n : ℕ) :
    -- `H^n_{X \ U}(V; ℚ) ≅ H^n(V, V ⊓ U; ℚ)`.
    ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X
      -- Sections over the open `V`.
      V).mapHomologicalComplex ℤᵘᵖ).obj
      -- `Γ_{X \ U}` of the singular-cochain sheaf complex.
      (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology (n : ℤ) ≃+
        -- `H^n` of the pair `(V, V ⊓ U)`.
        Singular.Cohomology.RelativeCohomology ℚ (Singular.SheafCochainOpenCone.openInclusionPair X (Opens.infLELeft V U)) n :=
  (SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V
      (SingularFlasqueModel.Singular.rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (HomologicalComplex.homologyMapIso
    (SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X
      (Singular.SheafCochain.singularCochainSheafComplex ℚ X) (Opens.infLELeft V U))
        ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans (Singular.SheafCochainOpenCone.openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft V U) n)

/-- Let `X` be a Hausdorff topological space whose every open subset is paracompact. Let `S ⊆ X` be
closed and `V ⊆ X` open. This identifies degree-`n` cohomology of sections on `V` of the
sheafified rational singular cochains supported in `S` with relative singular cohomology `H^n(V,
V \ S; ℚ)`. -/
def supportedRationalSingularSectionCohomologyEquivSupportComplement
    (S : Set X) (hS : IsClosed S) (V : Opens X) (n : ℕ) :
    -- `H^n_S(V; ℚ) ≅ H^n(V, V \ S; ℚ)`.
    ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X
      -- Sections over the open `V`.
      V).mapHomologicalComplex ℤᵘᵖ).obj
      -- `Γ_S` of the singular-cochain sheaf complex.
      (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ) ≃+
        -- `H^n` of the pair `(V, V \ S)`.
        Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (V : Set X) S) n :=
  (supportedRationalSingularSectionCohomologyEquivRelative X ⟨Sᶜ, hS.isOpen_compl⟩ V n).trans
    (((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
      (Algebra.Homology.LinearDual.HomologicalComplex.linearDualIso ((Singular.Cohomology.relativeChainFunctor ℚ).mapIso
        (openIntersectionPairIsoSupportComplement X S hS V).symm))).toLinearEquiv.toAddEquiv)

end

end OAI.AlgebraicTopology.Support.SingularSectionCohomology.Singular
