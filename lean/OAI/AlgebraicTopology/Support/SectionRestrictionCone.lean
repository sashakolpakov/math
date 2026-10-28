/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.FlasqueSections
import OAI.AlgebraicTopology.Support.FlasqueComparison
import OAI.Algebra.Homology.MapExtend

/-! # Section Restriction Cone -/

namespace OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Supported-section kernels and open restriction cones

For a termwise flasque coefficient complex, the kernel-defined supported section complex
computes the cone of restriction from `V` to `V ∩ U`, with the conventional degree shift.
The arrow identification displays the open-intersection map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable (X : TopCat.{u})

/-- Let `X` be a topological space and `W ⊆ V` open subsets. This natural transformation sends a
sheaf of abelian groups `F` to its restriction map `F(V) → F(W)`. -/
def supportEvaluationRestriction {V W : Opens X} (i : W ⟶ V) :
    DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V ⟶ DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W where
  app F := F.obj.map i.op
  naturality _F _G f := (f.hom.naturality i.op).symm

/-- Let `X` be a topological space, `W ⊆ V` open subsets, and `K` a complex of sheaves of abelian
groups with any specified grading. This map of section complexes `K(V) → K(W)` restricts
sections in each degree. -/
def sectionComplexRestriction {I : Type*} (c : ComplexShape I)
    (K : HomologicalComplex (Sheaf AddCommGrpCat.{u} X) c)
    {V W : Opens X} (i : W ⟶ V) :
    ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex c).obj K ⟶
      ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W).mapHomologicalComplex c).obj K :=
  ((supportEvaluationRestriction X i).mapHomologicalComplex c).app K

/-- Section restriction commutes with extension from natural to integer degrees. -/
theorem sectionComplexRestriction_extend
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    sectionComplexRestriction X ℤᵘᵖ (K.extend ComplexShape.embeddingUpNat) i ≫
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W) K
        ComplexShape.embeddingUpNat).hom =
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V) K
        ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
        ComplexShape.embeddingUpNat :=
  Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_natTrans (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V) K
    ComplexShape.embeddingUpNat (supportEvaluationRestriction X i)

/-- Let `X` be a topological space, `W ⊆ V` open subsets, and `K` a nonnegative complex of sheaves
of abelian groups. The two ways to extend the restriction map `K(V) → K(W)` by zero to negative
degrees give canonically isomorphic mapping cones: extend the sheaf complex before taking
sections, or extend the resulting section complexes. -/
def sectionComplexRestrictionExtendConeIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    CochainComplex.mappingCone
      (sectionComplexRestriction X ℤᵘᵖ (K.extend ComplexShape.embeddingUpNat) i) ≅
      CochainComplex.mappingCone
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
          ComplexShape.embeddingUpNat) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
    (Arrow.isoMk
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V) K
        ComplexShape.embeddingUpNat)
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W) K
        ComplexShape.embeddingUpNat)
      (sectionComplexRestriction_extend X K i).symm)

variable (U V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. For `j: U → X`, this is the degreewise identification `Γ(V,
j_*(K|_U)) ≅ K(V ∩ U)`. It identifies the last complex in the sequence of supported sections,
all sections, and restricted sections. -/
def supportRestrictionSectionsIntersectionIso :
    (DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).X₃ ≅
      ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X (V ⊓ U)).mapHomologicalComplex ℤᵘᵖ).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => DerivedSections.TopCat.Sheaf.supportedOutsideIntersectionIso X U V (K.X n))
    (fun n m _ => (K.d n m).hom.naturality
      (eqToHom (congrArg op (Opens.functor_map_eq_inf U V))))

/-- The intersection identification preserves the restriction arrow. -/
theorem supportRestrictionSectionsIntersectionIso_restriction :
    (DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).g ≫
      (supportRestrictionSectionsIntersectionIso X U V K).hom =
        sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U) :=
  HomologicalComplex.Hom.ext (funext fun n ↦
    FlasqueSections.TopCat.Sheaf.toOpenRestrictionPushforward_intersection X U V (K.X n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. The equality `Γ(V, j_*(K|_U)) ≅ K(V ∩ U)`, for `j: U → X`,
induces this isomorphism from the cone of `K(V) → Γ(V, j_*(K|_U))` to the cone of restriction
`K(V) → K(V ∩ U)`. -/
def supportRestrictionSectionsConeIso :
    CochainComplex.mappingCone (DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).g ≅
      CochainComplex.mappingCone
        (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U)) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
    (Arrow.isoMk (Iso.refl _) (supportRestrictionSectionsIntersectionIso X U V K)
      (by simpa using (supportRestrictionSectionsIntersectionIso_restriction X U V K).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. Assume every term of `K` is flasque, so its restriction maps
are surjective. Then sections on `V` vanishing on `V ∩ U` form the kernel of a surjective map of
complexes. This gives the isomorphism `H^n(Γ_{X \ U}(V, K)) ≅ H^{n-1}(Cone(K(V) → K(V ∩ U)))`. -/
def supportedSectionHomologyIsoRestrictionCone
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    -- `H^n(Γ_{X \ U}(V, K)) ≅ H^{n-1}(cone(K(V) → K(V ⊓ U)))`.
    -- `Γ_{X \ U}(V, K)`, the first term of `Γ_{X \ U}(V, K) → K(V) → K(V ⊓ U)`.
    (DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K).X₁.homology n ≅
      (CochainComplex.mappingCone
        -- The restriction `K(V) → K(V ⊓ U)`.
        (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U))).homology (n - 1) :=
  let S := DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V K
  letI : QuasiIso (Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    Algebra.Homology.DerivedCategoryMapOf.CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (FlasqueComparison.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK)
  let e := ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
    1 (n - 1) n (by omega)).app S.X₁
  e.symm ≪≫
    asIso (HomologicalComplex.homologyMap
      (Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)) ≪≫
    HomologicalComplex.homologyMapIso (supportRestrictionSectionsConeIso X U V K) (n - 1)

end

end OAI.AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf
