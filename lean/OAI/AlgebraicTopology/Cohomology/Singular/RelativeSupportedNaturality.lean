import OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SheafSections

/-! # Relative Supported Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

noncomputable section

/-!
# Naturality of the actual relative-to-supported comparison

The supported target is exactly the presheaf of section complexes of the
genuine supported singular sheaf complex. The canonical comparison commutes
with restrictions and hence defines a morphism of presheaves. Over a
characteristic-zero field on a metrizable space, its proved objectwise
quasi-isomorphisms induce a natural isomorphism of cohomology presheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) (O : Opens X)

/-- The actual presheaf of section complexes of the supported singular sheaf.
This is the standard `asFunctor` construction on its underlying presheaf complex. -/
abbrev supportedSingularSectionPresheaf :
    X.Presheaf (CochainComplex (ModuleCat.{0} R) ℕ) :=
  (SheafSections.sheafUnderlyingCochainComplex (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O)).asFunctor

@[simp]
theorem supportedSingularSectionPresheaf_obj (U : Opens X) :
    (supportedSingularSectionPresheaf M X O).obj (op U) =
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections M X O U := rfl

@[simp]
theorem supportedSingularSectionPresheaf_map {U V : Opens X} (i : U ⟶ V) :
    (supportedSingularSectionPresheaf M X O).map i.op =
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsRestriction M X O i := rfl

/-- Forgetting the support condition commutes with actual restriction
between open neighborhoods. -/
@[reassoc]
theorem supportedSingularSheafSectionsInclusion_naturality
    {U V : Opens X} (i : U ⟶ V) :
    AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsRestriction M X O i ≫
        AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U =
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O V ≫
        OpenSheafComparison.singularSheafSectionsRestriction M X i := by
  ext n : 1
  exact ((AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O
    (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))).f n).hom.naturality i.op

/-- The actual supported-section inclusion is a monomorphism of complexes. -/
instance supportedSingularSheafSectionsInclusion_mono (U : Opens X) :
    Mono (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U) := by
  rw [← AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsIsoKernel_inclusion]
  infer_instance

/-- Its maps on actual cochain modules are injective. -/
theorem supportedSingularSheafSectionsInclusion_f_injective (U : Opens X) (n : ℕ) :
    Function.Injective ((AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U).f n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The actual inclusion of supported sections forms a morphism of presheaves. -/
def supportedSingularSectionPresheafInclusion :
    supportedSingularSectionPresheaf M X O ⟶
      (SheafSections.sheafUnderlyingCochainComplex
        (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))).asFunctor where
  app U := AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U.unop
  naturality _ _ i := supportedSingularSheafSectionsInclusion_naturality M X O i.unop

@[simp]
theorem supportedSingularSectionPresheafInclusion_app (U : Opens X) :
    (supportedSingularSectionPresheafInclusion M X O).app (op U) =
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U := rfl

/-- The genuine relative-to-supported comparison commutes with restriction
of neighborhoods. It is determined by its actual inclusion into absolute sections. -/
@[reassoc]
theorem relativeToSupportedSheafSections_naturality {U V : Opens X} (i : U ⟶ V) :
    (RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X)).map i.op ≫
        SupportedRelativeMap.relativeToSupportedSheafSections M X O U =
      SupportedRelativeMap.relativeToSupportedSheafSections M X O V ≫
        AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsRestriction M X O i := by
  apply (cancel_mono (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U)).1
  calc
    _ = (RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X)).map i.op ≫
        RelativeSequence.relativeCochainInclusion M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) ≫
          OpenSheafComparison.singularCochainsToOpenSheafSections M X U := by
      rw [Category.assoc, SupportedRelativeMap.relativeToSupportedSheafSections_inclusion]
    _ = (RelativeSequence.relativeCochainInclusion M (TopCat.of V) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) V) ≫
        Singular.Functor.singularPullback M ((Opens.toTopCat X).map i)) ≫
          OpenSheafComparison.singularCochainsToOpenSheafSections M X U := by
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ OpenSheafComparison.singularCochainsToOpenSheafSections M X U)
        ((RelativeOpenSupport.relativeCochainPresheafInclusion M X (O : Set X)).naturality i.op)
    _ = RelativeSequence.relativeCochainInclusion M (TopCat.of V) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) V) ≫
        OpenSheafComparison.singularCochainsToOpenSheafSections M X V ≫
          OpenSheafComparison.singularSheafSectionsRestriction M X i := by
      rw [Category.assoc, OpenSheafComparison.singularCochainsToOpenSheafSections_naturality]
    _ = _ := by
      rw [Category.assoc, supportedSingularSheafSectionsInclusion_naturality,
        SupportedRelativeMap.relativeToSupportedSheafSections_inclusion_assoc]

/-- The canonical comparison is a morphism from the actual relative
cochain presheaf to the actual supported-section presheaf. -/
def relativeToSupportedSheafPresheafMap :
    RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X) ⟶
      (SheafSections.sheafUnderlyingCochainComplex (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O)).asFunctor where
  app U := SupportedRelativeMap.relativeToSupportedSheafSections M X O U.unop
  naturality _ _ i := relativeToSupportedSheafSections_naturality M X O i.unop

@[simp]
theorem relativeToSupportedSheafPresheafMap_app (U : Opens X) :
    (relativeToSupportedSheafPresheafMap M X O).app (op U) =
      SupportedRelativeMap.relativeToSupportedSheafSections M X O U := rfl

/-- Applying genuine homology yields the natural comparison on cohomology
presheaves, with the supported target in its standard section-cohomology model. -/
def relativeToSupportedCohomologyPresheafMap (n : ℕ) :
    RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n ⟶
      SheafSections.sheafSectionCohomologyPresheaf (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) n :=
  Functor.whiskerRight (relativeToSupportedSheafPresheafMap M X O)
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n)

@[simp]
theorem relativeToSupportedCohomologyPresheafMap_app (n : ℕ) (U : Opens X) :
    (relativeToSupportedCohomologyPresheafMap M X O n).app (op U) =
      HomologicalComplex.homologyMap (SupportedRelativeMap.relativeToSupportedSheafSections M X O U) n := rfl

/-- On a metrizable space, the proved actual openwise comparisons give
a natural isomorphism of relative and supported section-cohomology presheaves. -/
def relativeSupportedCohomologyPresheafIso
    (F : Type) [Field F] [CharZero F] (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (n : ℕ) :
    RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of F F) X (O : Set X) n ≅
      SheafSections.sheafSectionCohomologyPresheaf
        (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) n := by
  let f := relativeToSupportedCohomologyPresheafMap (ModuleCat.of F F) X O n
  have : IsIso f := (NatTrans.isIso_iff_isIso_app f).2 (by
    intro U
    have := SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable F X O U.unop
    change IsIso (HomologicalComplex.homologyMap
      (SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of F F) X O U.unop) n)
    infer_instance)
  exact asIso f

/-- The natural isomorphism's forward map is induced by the canonical
relative-to-supported cochain map on the specified open set. -/
@[simp]
theorem relativeSupportedCohomologyPresheafIso_hom_app
    (F : Type) [Field F] [CharZero F] (X : TopCat.{0}) [MetrizableSpace X]
    (O : Opens X) (n : ℕ) (U : Opens X) :
    (relativeSupportedCohomologyPresheafIso F X O n).hom.app (op U) =
      HomologicalComplex.homologyMap
        (SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of F F) X O U) n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality
