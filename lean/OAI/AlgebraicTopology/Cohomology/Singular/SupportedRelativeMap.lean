import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport
import OAI.AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso
import OAI.AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso

/-! # Supported Relative Map -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap

noncomputable section

/-!
# Actual relative cochains and supported singular-sheaf sections

The genuine open-section sheafification units give a map between the kernels
of restriction to an open complement. The two kernel sequences are short
exact, so the proved first-term five lemma gives a quasi-isomorphism whenever
the absolute and open-complement unit maps are quasi-isomorphisms. The source
kernel is identified with the existing actual relative singular cochains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) (O U : Opens X)

/-- The actual sheafification units induce the canonical map between the
two restriction kernels on an open neighborhood. -/
def openSupportedSingularKernelComparison :
    kernel (RelativeOpenSupport.openSupportCochainRestriction X M O U) ⟶
      kernel (OpenSheafComparison.singularSheafSectionsRestriction M X
        (homOfLE (inf_le_left : U ⊓ O ≤ U))) :=
  kernel.map (RelativeOpenSupport.openSupportCochainRestriction X M O U)
    (OpenSheafComparison.singularSheafSectionsRestriction M X (homOfLE (inf_le_left : U ⊓ O ≤ U)))
    (OpenSheafComparison.singularCochainsToOpenSheafSections M X U)
    (OpenSheafComparison.singularCochainsToOpenSheafSections M X (U ⊓ O))
    (OpenSheafComparison.singularCochainsToOpenSheafSections_naturality M X
      (homOfLE (inf_le_left : U ⊓ O ≤ U)))

/-- On underlying absolute cochains, the kernel comparison is precisely
the genuine open-section unit. -/
@[reassoc (attr := simp)]
theorem openSupportedSingularKernelComparison_inclusion :
    openSupportedSingularKernelComparison M X O U ≫
        kernel.ι (OpenSheafComparison.singularSheafSectionsRestriction M X
          (homOfLE (inf_le_left : U ⊓ O ≤ U))) =
      kernel.ι (RelativeOpenSupport.openSupportCochainRestriction X M O U) ≫
        OpenSheafComparison.singularCochainsToOpenSheafSections M X U :=
  kernel.lift_ι _ _ _

/-- The same canonical kernel map, with codomain the actual sections of
the supported singular cochain sheaf complex. -/
def openSupportedSingularComparison :
    kernel (RelativeOpenSupport.openSupportCochainRestriction X M O U) ⟶
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections M X O U :=
  openSupportedSingularKernelComparison M X O U ≫
    (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsIsoKernel M X O U).inv

/-- Forgetting support after comparison is exactly the absolute unit. -/
@[reassoc (attr := simp)]
theorem openSupportedSingularComparison_inclusion :
    openSupportedSingularComparison M X O U ≫
        AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U =
      kernel.ι (RelativeOpenSupport.openSupportCochainRestriction X M O U) ≫
        OpenSheafComparison.singularCochainsToOpenSheafSections M X U := by
  rw [openSupportedSingularComparison, Category.assoc,
    ← AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsIsoKernel_inclusion]
  rw [Iso.inv_hom_id_assoc, openSupportedSingularKernelComparison_inclusion]

/-- The canonical actual relative-to-supported comparison on an open set. -/
def relativeToSupportedSheafSections :
    RelativeSequence.relativeSingularCochains M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) ⟶
      AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections M X O U :=
  (RelativeOpenSupport.relativeOpenSupportKernelIso X M O U).hom ≫
    openSupportedSingularComparison M X O U

/-- The comparison preserves the intended relative cochain in the ambient
absolute complex, through the actual sheafification unit. -/
@[reassoc (attr := simp)]
theorem relativeToSupportedSheafSections_inclusion :
    relativeToSupportedSheafSections M X O U ≫
        AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O U =
      RelativeSequence.relativeCochainInclusion M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) ≫
        OpenSheafComparison.singularCochainsToOpenSheafSections M X U := by
  rw [relativeToSupportedSheafSections, Category.assoc,
    openSupportedSingularComparison_inclusion, ← Category.assoc,
    RelativeOpenSupport.relativeOpenSupportKernelIso_inclusion]

/-- The canonical comparison is a morphism of the two genuine kernel
sequences, with the actual absolute and open-complement units. -/
def openSupportedKernelSequenceMap :
    SurjectiveQuasiIso.cochainKernelSequence (RelativeOpenSupport.openSupportCochainRestriction X M O U) ⟶
      SurjectiveQuasiIso.cochainKernelSequence (OpenSheafComparison.singularSheafSectionsRestriction M X
        (homOfLE (inf_le_left : U ⊓ O ≤ U))) where
  τ₁ := openSupportedSingularKernelComparison M X O U
  τ₂ := OpenSheafComparison.singularCochainsToOpenSheafSections M X U
  τ₃ := OpenSheafComparison.singularCochainsToOpenSheafSections M X (U ⊓ O)
  comm₁₂ := openSupportedSingularKernelComparison_inclusion M X O U
  comm₂₃ := (OpenSheafComparison.singularCochainsToOpenSheafSections_naturality M X
    (homOfLE (inf_le_left : U ⊓ O ≤ U))).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap
