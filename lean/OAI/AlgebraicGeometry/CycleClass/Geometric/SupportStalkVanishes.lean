import OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport
import OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

/-! # Support Stalk Vanishes -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes

noncomputable section

section

/-!
# The actual singular cochain sheaf complex with closed supports

The supported complex is the categorical kernel of restriction to the open
complement. Taking sections preserves this kernel. The comparison from
ordinary relative singular cochains is induced by the genuine sheafification
unit, with no assumed local purity or manifold structure of the closed support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cohomology

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- Restriction to an open set followed by pushforward, degree by degree. -/
def openRestrictionSheafComplex (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ :=
  ((SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The actual restriction map of sheaf complexes. -/
def sheafRestrictionComplex (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    K ⟶ openRestrictionSheafComplex O K where
  f n := SheafClosedSupport.Cohomology.sheafRestrictionToOpen O (K.X n)
  comm' i j _ := ((SheafClosedSupport.Cohomology.sheafRestrictionToOpenNatTrans O).naturality (K.d i j)).symm

/-- The actual kernel complex of sheaf sections supported on `X \ O`. -/
def supportedSheafComplex (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ :=
  kernel (sheafRestrictionComplex O K)

/-- The inclusion from the supported complex. -/
def supportedSheafComplexInclusion (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    supportedSheafComplex O K ⟶ K :=
  kernel.ι (sheafRestrictionComplex O K)

/-- Each degree is canonically the actual supported sheaf in that degree. -/
def supportedSheafComplexDegreeIso (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) (n : ℕ) :
    (supportedSheafComplex O K).X n ≅ SheafClosedSupport.Cohomology.closedSupportSheaf O (K.X n) :=
  PreservesKernel.iso
    (HomologicalComplex.eval (TopCat.Sheaf (ModuleCat.{0} R) X) (ComplexShape.up ℕ) n)
    (sheafRestrictionComplex O K)

@[reassoc (attr := simp)]
theorem supportedSheafComplexDegreeIso_inclusion (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) (n : ℕ) :
    (supportedSheafComplexDegreeIso O K n).hom ≫ SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X n) =
      (supportedSheafComplexInclusion O K).f n := by
  change (PreservesKernel.iso
    (HomologicalComplex.eval (TopCat.Sheaf (ModuleCat.{0} R) X) (ComplexShape.up ℕ) n)
    (sheafRestrictionComplex O K)).hom ≫ _ = _
  rw [PreservesKernel.iso_hom]
  convert kernelComparison_comp_ι (sheafRestrictionComplex O K)
      (HomologicalComplex.eval (TopCat.Sheaf (ModuleCat.{0} R) X) (ComplexShape.up ℕ) n)
    using 1 <;> rfl

/-- Evaluate an actual complex of module sheaves on an open subset. -/
def moduleSheafSectionsComplex (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- Actual restriction of the sections of a complex of module sheaves. -/
def moduleSheafSectionsRestriction
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    {U V : Opens X} (i : U ⟶ V) :
    moduleSheafSectionsComplex V K ⟶ moduleSheafSectionsComplex U K where
  f n := (K.X n).obj.map i.op
  comm' p q _ := (K.d p q).hom.naturality i.op

/-- Sections of the supported complex are the actual kernel of restriction
from the open set to its intersection with the open complement. -/
def supportedSheafSectionsIsoKernel (O U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    moduleSheafSectionsComplex U (supportedSheafComplex O K) ≅
      kernel (moduleSheafSectionsRestriction K
        (homOfLE (inf_le_left : U ⊓ O ≤ U))) :=
  PreservesKernel.iso
    ((SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ))
    (sheafRestrictionComplex O K)

/-- The singular cochain sheaf complex with support in `X \ O`. -/
def supportedSingularSheafComplex (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O : Opens X) : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ :=
  supportedSheafComplex O
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))

/-- Actual sections of the supported singular cochain sheaf complex. -/
def supportedSingularSheafSections (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O U : Opens X) : CochainComplex (ModuleCat.{0} R) ℕ :=
  moduleSheafSectionsComplex U (supportedSingularSheafComplex M X O)

/-- Restrict supported singular sections to a smaller open set. -/
def supportedSingularSheafSectionsRestriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O : Opens X) {U V : Opens X} (i : U ⟶ V) :
    supportedSingularSheafSections M X O V ⟶ supportedSingularSheafSections M X O U :=
  moduleSheafSectionsRestriction (supportedSingularSheafComplex M X O) i

/-- Inclusion of supported singular sections into all singular sheaf sections. -/
def supportedSingularSheafSectionsInclusion (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O U : Opens X) :
    supportedSingularSheafSections M X O U ⟶ AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSections M X U :=
  ((SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (supportedSheafComplexInclusion O
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)))

/-- The actual kernel identification for supported singular sections. -/
def supportedSingularSheafSectionsIsoKernel (M : ModuleCat.{0} R) (X : TopCat.{0})
    (O U : Opens X) :
    supportedSingularSheafSections M X O U ≅
      kernel (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSectionsRestriction M X
        (homOfLE (inf_le_left : U ⊓ O ≤ U))) :=
  supportedSheafSectionsIsoKernel O U
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))

@[reassoc (attr := simp)]
theorem supportedSingularSheafSectionsIsoKernel_inclusion
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (O U : Opens X) :
    (supportedSingularSheafSectionsIsoKernel M X O U).hom ≫
      kernel.ι (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSectionsRestriction M X
        (homOfLE (inf_le_left : U ⊓ O ≤ U))) =
      supportedSingularSheafSectionsInclusion M X O U := by
  change (PreservesKernel.iso
    ((SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ))
    (sheafRestrictionComplex O
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)))).hom ≫ _ = _
  rw [PreservesKernel.iso_hom]
  convert kernelComparison_comp_ι
      (sheafRestrictionComplex O
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)))
      ((SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ))
    using 1 <;> rfl

end Cohomology

end

/-!
# Actual supported sheaf stalks outside their support

A section of the kernel sheaf with support in `X \ O` is zero on every
open subset of `O`. Every germ based in `O` has such a representative, so
the actual stalk is zero. No purity or regularity hypothesis is involved.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {R : Type} [Ring R] {X : TopCat.{0}}

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

/-- Supported sections vanish on any actual open set contained in the open
complement of the support. -/
theorem closedSupportSheaf_section_eq_zero (O U : Opens X) (hU : U ≤ O)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X)
    (s : (SheafClosedSupport.Cohomology.closedSupportSheaf O F).obj.obj (op U)) : s = 0 := by
  have hi : IsIso (homOfLE (inf_le_left : U ⊓ O ≤ U)) := by
    let e : U ⊓ O ≅ U :=
      { hom := homOfLE inf_le_left
        inv := homOfLE (le_inf le_rfl hU)
        hom_inv_id := Subsingleton.elim _ _
        inv_hom_id := Subsingleton.elim _ _ }
    exact e.isIso_hom
  apply SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective O U F
  rw [map_zero]
  apply (ModuleCat.mono_iff_injective
    (F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op)).1 inferInstance
  simpa only [map_zero] using SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes O U F s

/-- Every germ of the actual supported sheaf vanishes at a point of the
open complement. -/
theorem closedSupportSheaf_germ_eq_zero (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) (x : X) (hx : x ∈ O)
    (s : (SheafClosedSupport.Cohomology.closedSupportSheaf O F).presheaf.stalk x) : s = 0 := by
  obtain ⟨U, hU, hxU, t, rfl⟩ :=
    (SheafClosedSupport.Cohomology.closedSupportSheaf O F).presheaf.exists_le_germ_eq s hx
  rw [closedSupportSheaf_section_eq_zero O U hU F t, map_zero]

/-- The actual stalk object of the supported sheaf is zero outside its
closed support. -/
theorem closedSupportSheaf_stalk_isZero (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) (x : X) (hx : x ∈ O) :
    IsZero ((SheafClosedSupport.Cohomology.closedSupportSheaf O F).presheaf.stalk x) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact subsingleton_of_forall_eq 0 (closedSupportSheaf_germ_eq_zero O F x hx)

/-- Every degree of the actual supported stalk complex is zero at a point
of the open complement. -/
theorem supportedSheafComplex_stalk_X_isZero (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (x : X) (hx : x ∈ O) (n : ℕ) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (Cohomology.supportedSheafComplex O K) x).X n) :=
  (closedSupportSheaf_stalk_isZero O (K.X n) x hx).of_iso
    ((TopCat.Sheaf.forget (ModuleCat.{0} R) X ⋙ stalkFunctor (ModuleCat.{0} R) x).mapIso
      (Cohomology.supportedSheafComplexDegreeIso O K n))

/-- The supported stalk complex is exact in every degree outside the
closed support. -/
theorem supportedSheafComplex_stalk_exactAt_of_mem (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (x : X) (hx : x ∈ O) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (Cohomology.supportedSheafComplex O K) x).ExactAt n :=
  HomologicalComplex.ExactAt.of_isZero
    (supportedSheafComplex_stalk_X_isZero O K x hx n)

/-- In particular all the actual supported stalk cohomology objects vanish. -/
theorem supportedSheafComplex_stalk_homology_isZero_of_mem (O : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)
    (x : X) (hx : x ∈ O) (n : ℕ) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (Cohomology.supportedSheafComplex O K) x).homology n) :=
  (supportedSheafComplex_stalk_exactAt_of_mem O K x hx n).isZero_homology

/-- The genuine supported singular cochain stalk has zero cohomology off
the support, with arbitrary module coefficients and in every degree. -/
theorem supportedSingularSheaf_stalk_homology_isZero_of_mem
    (M : ModuleCat.{0} R) (O : Opens X) (x : X) (hx : x ∈ O) (n : ℕ) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (Cohomology.supportedSingularSheafComplex M X O) x).homology n) :=
  supportedSheafComplex_stalk_homology_isZero_of_mem O
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)) x hx n

/-- The actual cohomology sheaf also has zero stalk on the open complement,
via the proved stalk--cohomology comparison. -/
theorem supportedSingularSheaf_cohomologySheaf_stalk_isZero_of_mem
    (M : ModuleCat.{0} R) (O : Opens X) (x : X) (hx : x ∈ O) (n : ℕ) :
    IsZero (((Cohomology.supportedSingularSheafComplex M X O).homology n).presheaf.stalk x) :=
  (supportedSingularSheaf_stalk_homology_isZero_of_mem M O x hx n).of_iso
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso (Cohomology.supportedSingularSheafComplex M X O) x n).symm

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes
