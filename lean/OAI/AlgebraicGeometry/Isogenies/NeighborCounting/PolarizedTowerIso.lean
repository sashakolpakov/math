import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Polarized Tower Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso

noncomputable section

/-! The actual scalar-tower group comparison underlies a full
polarized and ordered-level isomorphism of the original source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison

variable {S T U : Scheme} {d N : ℕ} {δ : Fin d → ℕ}

def polarizedBaseCongrIso (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N S)
    (f g : T ⟶ S) (w : f = g) : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback g) := by
  cases w
  exact AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl _

def polarizedIteratedIso (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N S)
    (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.pullback f).pullback h) (A.pullback g) :=
  (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f h).trans (polarizedBaseCongrIso A (h ≫ f) g w)

theorem polarizedIteratedIso_abelian (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N S)
    (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g) :
    (polarizedIteratedIso A f h g w).abelian = PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.abelian.scheme f h g w := by
  cases w
  apply Iso.ext
  change (A.abelian.pullbackCompIso f h).inv ≫ 𝟙 _ =
    (PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso A.abelian.scheme f h).inv ≫ PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.congrMap A.abelian.scheme (h ≫ f) (h ≫ f) rfl
  rw [PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.congrMap_self, Category.comp_id, Category.comp_id, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  rfl

variable (R F L : Type) [CommRing R] [IsLocalRing R] [Field F] [Field L]
  [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of R))) (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedIntegralPolarizedIso :=
  (polarizedIteratedIso A
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Evaluated.BlockSplitting.algebraTowerBaseComp R F L)).trans
  (polarizedIteratedIso A
    (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Evaluated.BlockSplitting.algebraTowerBaseComp R v.carrier L)).symm

theorem evaluatedIntegralPolarizedIso_abelian :
    (evaluatedIntegralPolarizedIso R F L A v).abelian =
      Evaluated.BlockSplitting.evaluatedIntegralBlockIso R F L A.abelian.scheme v := by
  change (polarizedIteratedIso A _ _ _ (Evaluated.BlockSplitting.algebraTowerBaseComp R F L)).abelian ≪≫
    (polarizedIteratedIso A _ _ _ (Evaluated.BlockSplitting.algebraTowerBaseComp R v.carrier L)).abelian.symm = _
  rw [polarizedIteratedIso_abelian, polarizedIteratedIso_abelian]
  rfl

theorem evaluatedIntegralPolarizedIso_group_hom :
    (evaluatedIntegralPolarizedIso R F L A v).abelian.hom =
      (Evaluated.BlockGroupComparison.evaluatedIntegralBlockGroupIso R F L (Grp.mk A.abelian.scheme) v).hom.hom.hom :=
  congrArg Iso.hom (evaluatedIntegralPolarizedIso_abelian R F L A v)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedTowerIso
