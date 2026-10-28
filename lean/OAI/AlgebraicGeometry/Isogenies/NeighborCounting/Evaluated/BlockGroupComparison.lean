import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPullback
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

/-! # Block Group Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison

noncomputable section

/-! The scalar-tower and evaluation-DVR comparisons preserve the
actual group structures on native torsion blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockSplitting
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

variable (R F L : Type) [CommRing R] [IsLocalRing R] [Field F] [Field L]
  [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]

def evaluatedIntegralBlockGroupIso (G : Grp (Over (Spec (.of R)))) (v : EvaluationDVRLifts.EvaluationDVR R L) :=
  SplitBlockPullback.iteratedBlockGroupIso G
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (BlockSplitting.algebraTowerBaseComp R F L) ≪≫
  (SplitBlockPullback.iteratedBlockGroupIso G
    (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (BlockSplitting.algebraTowerBaseComp R v.carrier L)).symm

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (v : EvaluationDVRLifts.EvaluationDVR R L) (n : ℕ) (τ : Gal(E/ℚ))
  {H : Grp (Over (Spec (.of v.carrier)))}
  (eH : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).mapGrp.obj
    (Lifted.GeometricBlockIso.nativeActionBlockGroup A ρ (q ^ n) (j.projector iota hsplit n τ)) ≅ H)

def evaluatedNativeBlockGroupIso :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.mapIso
    (Intrinsic.BlockBaseChange.nativeBlockBaseChangeGroupIso j iota hsplit A ρ
      (Spec.map (CommRingCat.ofHom (algebraMap R F))) n τ).symm ≪≫
    evaluatedIntegralBlockGroupIso R F L
      (Lifted.GeometricBlockIso.nativeActionBlockGroup A ρ (q ^ n) (j.projector iota hsplit n τ)) v ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).mapGrp.mapIso eH

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
