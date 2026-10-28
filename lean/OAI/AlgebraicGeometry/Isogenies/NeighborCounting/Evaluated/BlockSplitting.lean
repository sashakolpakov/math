import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

/-! # Block Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting

noncomputable section

/-! Transfer a splitting of the original generic block to the
generic fiber over its actual evaluation DVR. Both comparisons use
the scalar-tower equations of the original ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts

theorem algebraTowerBaseComp (R K L : Type) [CommRing R] [CommRing K] [CommRing L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L] :
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) =
    Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a => (IsScalarTower.algebraMap_apply R K L a).symm)

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (A : Over (Spec (.of R))) [GrpObj A]

def scalarTowerBlockIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A :=
  PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (algebraTowerBaseComp R K L)

variable [IsLocalRing R] (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedIntegralBlockIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).obj A) :=
  scalarTowerBlockIso R K L A ≪≫
    (PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A
      (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
      (Spec.map (CommRingCat.ofHom (algebraMap R L))) (algebraTowerBaseComp R v.carrier L)).symm

def evaluatedIntegralBlockSplitting {I : Type}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).obj A) :=
  e ≪≫ evaluatedIntegralBlockIso R K L A v

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting
