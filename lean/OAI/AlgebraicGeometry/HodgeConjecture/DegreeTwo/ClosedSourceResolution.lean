import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedPushforwardExactness
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafZeroResolution

/-! # Closed Source Resolution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions

noncomputable section

section

/-! The independently constructed source resolution on the ambient space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

theorem closedSourceSheaf_positive_exact [StronglyLocallyContractibleSpace Y]
    (hf : Topology.IsClosedEmbedding f) (n : ℕ) :
    (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f).ExactAt (n+1) :=
  ClosedPushforwardExactness.Constructions.closedPushforwardSheafComplex_exactAt f hf (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y) (n+1)
    (SingularSheafZeroResolution.Constructions.rationalSingularSheaf_positive_exact Y n)

def closedSourceSheafAugmentation :
    (CochainComplex.single₀ _).obj
        ((SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f).homology 0) ⟶
      SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f :=
  ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)

theorem closedSourceSheafAugmentation_quasiIso [StronglyLocallyContractibleSpace Y]
    (hf : Topology.IsClosedEmbedding f) : QuasiIso (closedSourceSheafAugmentation f) :=
  ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_quasiIso (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) (by
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact (closedSourceSheaf_positive_exact f hf n).isZero_homology)

theorem closedSourceSheaf_isFlasque [MetrizableSpace Y] (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f).X n) := by
  have := AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) Y n
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) Y)).X n) f

/-- These section groups are the actual singular cohomology of the source preimage. -/
def closedSourceSheafSectionCohomologyIso [MetrizableSpace Y] (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U
      (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)).homology n ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U)) n := by
  have := AlgebraicTopology.Cohomology.Singular.OpenParacompact.paracompactSpace_open_of_metrizable Y ((Opens.map f).obj U)
  have := AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.quasiIso_singularCochainsToOpenSheafSections_of_paracompact ℚ Y ((Opens.map f).obj U)
  exact (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) Y
    ((Opens.map f).obj U)) n).symm

end

/-! Native source pullback is recovered exactly from the source sheaf section comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : Y ⟶ X)

theorem singularSheafPullback_sections_unit (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M X U ≫
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SingularSheafPullback.Constructions.singularSheafPullbackMap M f)) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (SingularSheafPullback.Constructions.openPreimageMap f U) ≫
        AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M Y ((Opens.map f).obj U) := by
  ext n : 1
  exact SingularSheafPullback.Constructions.singularSheafPullbackMap_unit M f U n

variable [MetrizableSpace Y]

theorem rationalSourceSheafPullback_sections_cohomology (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U) n ≫
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) f)) n ≫
        (closedSourceSheafSectionCohomologyIso f U n).hom =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (SingularSheafPullback.Constructions.openPreimageMap f U) n := by
  have := AlgebraicTopology.Cohomology.Singular.OpenParacompact.paracompactSpace_open_of_metrizable Y ((Opens.map f).obj U)
  have := AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.quasiIso_singularCochainsToOpenSheafSections_of_paracompact ℚ Y ((Opens.map f).obj U)
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    singularSheafPullback_sections_unit, HomologicalComplex.homologyMap_comp, Category.assoc]
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (SingularSheafPullback.Constructions.openPreimageMap f U)) n ≫
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj U)) n ≫
    (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) Y
      ((Opens.map f).obj U)) n).inv = _
  rw [isoOfQuasiIsoAt_hom_inv_id, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions
