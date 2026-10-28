import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstantSections
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitExtension

/-! # Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Splitting.Lifts

noncomputable section

/-!
Evaluated generic labels construct a section of the integral component
quotient and hence its product splitting. Its section equation is proved
by the uniqueness of extension, not included as integral input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (R L : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {G : Type u} [Group G]
variable (A : Over (Spec (.of R))) [GrpObj A] [IsProper A.hom]

/-- Assemble the extended evaluated labels into an actual group-scheme
map from the native constant group. -/
def evaluatedConstantMap (z : G →* (Sections.Lifts.genericTest R L ⟶ A)) :
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X ⟶ A :=
  ConstantSections.Lifts.mapFromConstantSections (Sections.Lifts.extendEvaluatedLabels R L A z)

instance evaluatedConstantMap_isMonHom (z : G →* (Sections.Lifts.genericTest R L ⟶ A)) :
    IsMonHom (evaluatedConstantMap R L A z) :=
  inferInstanceAs (IsMonHom (ConstantSections.Lifts.mapFromConstantSections (Sections.Lifts.extendEvaluatedLabels R L A z)))

theorem evaluatedConstantMap_generic_labels (z : G →* (Sections.Lifts.genericTest R L ⟶ A)) (g : G) :
    Sections.Lifts.sectionRestriction R L A
        (ConstantSections.Lifts.constantLabelSection (Spec (.of R)) G g ≫ evaluatedConstantMap R L A z) = z g := by
  rw [evaluatedConstantMap, ConstantSections.Lifts.constantLabelSection_map, Sections.Lifts.extendEvaluatedLabels_generic]

variable [Finite G]
variable (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X) [IsMonHom π]
variable (z : G →* (Sections.Lifts.genericTest R L ⟶ A))
variable (hz : ∀ g, z g ≫ π = Sections.Lifts.sectionRestriction R L
  (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X (ConstantSections.Lifts.constantLabelSection (Spec (.of R)) G g))

include hz in
omit [IsMonHom π] in
/-- The generic component labels force the integral section equation by
uniqueness of extension into the proper constant scheme. -/
theorem evaluated_component_section : evaluatedConstantMap R L A z ≫ π = 𝟙 _ := by
  apply ConstantSections.Lifts.constantMaps_ext
  intro g
  apply (Sections.Lifts.sectionRestriction_bijective R L (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X).1
  change (toUnit (Sections.Lifts.genericTest R L) ≫
      (ConstantSections.Lifts.constantLabelSection (Spec (.of R)) G g ≫ evaluatedConstantMap R L A z)) ≫ π = _
  have hg := evaluatedConstantMap_generic_labels R L A z g
  change toUnit (Sections.Lifts.genericTest R L) ≫
    (ConstantSections.Lifts.constantLabelSection (Spec (.of R)) G g ≫ evaluatedConstantMap R L A z) = z g at hg
  rw [hg]
  exact (hz g).trans (congrArg (Sections.Lifts.sectionRestriction R L
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X) (Category.comp_id _).symm)

variable [IsCommMonObj A]

/-- The evaluated lift has a constructed split block with its actual
scheme-theoretic connected kernel, including nonreduced torsion. -/
def evaluatedComponentSplit :
    Picard.PoincareBundle.Kernel.Scheme.kernelObject π ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) G).X ≅ A :=
  SplitExtension.Lifts.splitExtensionIso π (evaluatedConstantMap R L A z)
    (evaluated_component_section R L A π z hz)

instance evaluatedComponentSplit_isMonHom : IsMonHom (evaluatedComponentSplit R L A π z hz).hom :=
  inferInstanceAs (IsMonHom (SplitExtension.Lifts.splitExtensionIso π (evaluatedConstantMap R L A z)
    (evaluated_component_section R L A π z hz)).hom)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Splitting.Lifts
