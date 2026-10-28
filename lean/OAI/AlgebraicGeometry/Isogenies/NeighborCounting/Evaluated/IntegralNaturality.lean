import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedBaseChangeNaturality

/-! # Integral Naturality -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntegralNaturality

noncomputable section

/-! The two actual scalar towers retain every ambient inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedBaseChangeNaturality

variable (R F L : Type) [CommRing R] [IsLocalRing R] [Field F] [Field L]
  [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {A B : Over (Spec (.of R))}
  (v : EvaluationDVRLifts.EvaluationDVR R L) (a : A ⟶ B)

theorem evaluatedIntegralBlockIso_natural :
    (BlockSplitting.evaluatedIntegralBlockIso R F L A v).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).map a) =
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map a) ≫
      (BlockSplitting.evaluatedIntegralBlockIso R F L B v).hom := by
  exact IteratedBaseChangeNaturality.iso_comparison_natural _ _ _ _ _ _ _
    (IteratedBaseChangeNaturality.iteratedIso_natural _ _ _ (BlockSplitting.algebraTowerBaseComp R F L) a)
    (IteratedBaseChangeNaturality.iteratedIso_natural _ _ _ (BlockSplitting.algebraTowerBaseComp R v.carrier L) a)

theorem evaluatedIntegralBlockGroupIso_natural
    (G H : Grp (Over (Spec (.of R)))) (i : G ⟶ H) :
    (BlockGroupComparison.evaluatedIntegralBlockGroupIso R F L G v).hom.hom.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).map i.hom.hom) =
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map i.hom.hom) ≫
      (BlockGroupComparison.evaluatedIntegralBlockGroupIso R F L H v).hom.hom.hom :=
  evaluatedIntegralBlockIso_natural R F L v i.hom.hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntegralNaturality
