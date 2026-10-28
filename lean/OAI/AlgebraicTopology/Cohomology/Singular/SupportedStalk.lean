import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeStalk
import OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionStalk

/-! # Supported Stalk -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk

noncomputable section

/-!
# Supported singular-sheaf stalk cohomology

For the actual kernel of singular-sheaf restriction to an open complement,
stalk cohomology is the filtered colimit of the genuine relative groups
`Hⁿ(U, U ∩ O)`. The comparison uses the proved open-section comparison on
metrizable spaces and actual restriction maps. In particular, no interchange
of sheafification with open direct image is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Germs

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
  (X : TopCat.{0}) (O : Opens X)

/-- Send a genuine relative cochain to the actual supported-sheaf stalk by
the actual open-section comparison followed by its germ. -/
def relativeToSupportedStalkGerm (U : Opens X) (x : X) (hx : x ∈ U) :
    RelativeSequence.relativeSingularCochains M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) ⟶
      SheafQuasiIso.sheafStalkCochainComplex (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) x :=
  SupportedRelativeMap.relativeToSupportedSheafSections M X O U ≫
    SheafSectionStalk.sheafSectionCochainGerm (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) U x hx

/-- The supported-stalk map commutes with the actual restriction of pairs. -/
@[reassoc]
theorem relativeToSupportedStalkGerm_restrict {U V : Opens X} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) :
    (RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X)).map i.op ≫
        relativeToSupportedStalkGerm M X O U x hx =
      relativeToSupportedStalkGerm M X O V x (i.le hx) := by
  dsimp only [relativeToSupportedStalkGerm]
  rw [← Category.assoc, RelativeSupportedNaturality.relativeToSupportedSheafSections_naturality, Category.assoc]
  congr 1
  exact SheafSectionStalk.sheafSectionCochainGerm_restrict (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) i x hx

end Germs

variable (F : Type) [Field F] [CharZero F]
  (X : TopCat.{0}) [MetrizableSpace X] (O : Opens X)

/-- The cohomology of the actual supported singular-sheaf stalk is the
filtered colimit of actual neighborhood relative cohomology. -/
def supportedStalkRelativeCohomologyIso (x : X) (n : ℕ) :
    (SheafQuasiIso.sheafStalkCochainComplex
      (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x).homology n ≅
      colimit (RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of F F) X (O : Set X) x n) :=
  SheafSectionStalk.sheafSectionStalkCohomologyIso
      (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x n ≪≫
    (stalkFunctor (ModuleCat.{0} F) x).mapIso
      (RelativeSupportedNaturality.relativeSupportedCohomologyPresheafIso F X O n).symm

/-- The comparison identifies the genuine germ of a relative class with
the canonical injection into its filtered neighborhood colimit. -/
@[reassoc]
theorem supportedStalkRelativeCohomologyIso_germ
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    HomologicalComplex.homologyMap
        (relativeToSupportedStalkGerm (ModuleCat.of F F) X O U x hx) n ≫
        (supportedStalkRelativeCohomologyIso F X O x n).hom =
      colimit.ι (RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of F F) X (O : Set X) x n)
        (op ⟨U, hx⟩) := by
  change HomologicalComplex.homologyMap
      (SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of F F) X O U ≫
        SheafSectionStalk.sheafSectionCochainGerm
          (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) U x hx) n ≫
    ((SheafSectionStalk.sheafSectionStalkCohomologyIso
      (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x n).hom ≫
      (stalkFunctor (ModuleCat.{0} F) x).map
        (RelativeSupportedNaturality.relativeSupportedCohomologyPresheafIso F X O n).inv) = _
  rw [HomologicalComplex.homologyMap_comp, Category.assoc,
    SheafSectionStalk.sheafSectionStalkCohomologyIso_germ_assoc, stalkFunctor_map_germ,
    ← RelativeSupportedNaturality.relativeSupportedCohomologyPresheafIso_hom_app]
  change ((RelativeSupportedNaturality.relativeSupportedCohomologyPresheafIso F X O n).app (op U)).hom ≫
    ((RelativeSupportedNaturality.relativeSupportedCohomologyPresheafIso F X O n).app (op U)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The same comparison for the stalk of the genuine supported cohomology
sheaf, using exactness of stalks on module sheaves. -/
def supportedHomologySheafStalkRelativeIso (x : X) (n : ℕ) :
    TopCat.Presheaf.stalk (X := X)
      ((AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O).homology n).obj x ≅
      colimit (RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of F F) X (O : Set X) x n) :=
  (SheafQuasiIso.sheafStalkCohomologyIso
      (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x n).symm ≪≫
    supportedStalkRelativeCohomologyIso F X O x n

/-- Actual supported-stalk exactness is equivalent to vanishing of the
filtered colimit of the genuine local relative cohomology groups. -/
theorem supportedStalk_exactAt_iff_relativeColimit (x : X) (n : ℕ) :
    (SheafQuasiIso.sheafStalkCochainComplex
      (AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x).ExactAt n ↔
      IsZero (colimit
        (RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of F F) X (O : Set X) x n)) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h => h.of_iso (supportedStalkRelativeCohomologyIso F X O x n).symm,
    fun h => h.of_iso (supportedStalkRelativeCohomologyIso F X O x n)⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk
