import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange

/-! # Block Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange

noncomputable section

/-! Base change of the actual IsogenyQuotient fixed-kernel block, retaining its
original inclusion into the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange.Construction

local instance nativeBlockPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S S' : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (f : S' ⟶ S) (n : ℕ) (τ : Gal(E/ℚ))

def nativeBlockBaseChangeGroupIso :
    (Over.pullback f).mapGrp.obj
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)))) ≅
    Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) ((ρ.pullback f).map (j.projector iota hsplit n τ))) :=
  (Over.pullback f).mapGrp.mapIso (CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit A ρ n τ) ≪≫
    AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ f n τ ≪≫
      (CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit (A.pullback f) (ρ.pullback f) n τ).symm

def l45BlockBaseChangeOverIso :
    (Over.pullback f).obj (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ)) ≅
      PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme (A.pullback f) (ρ.pullback f) (q ^ n) (j.projector iota hsplit n τ) :=
  (Grp.forget _).mapIso (AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ f n τ)

theorem l45BlockBaseChangeOverIso_inclusion :
    (l45BlockBaseChangeOverIso j iota hsplit A ρ f n τ).hom ≫
      CMPointsBlockComparison.l45BlockInclusion j iota hsplit (A.pullback f) (ρ.pullback f) n τ =
    (Over.pullback f).map (CMPointsBlockComparison.l45BlockInclusion j iota hsplit A ρ n τ) :=
  AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso_inclusion j iota hsplit A ρ f n τ

theorem nativeCMPointsBlockIso_inv_inclusion :
    (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A ρ n τ).inv ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) =
        CMPointsBlockComparison.l45BlockInclusion j iota hsplit A ρ n τ := by
  rw [← CMPointsBlockComparison.l45NativeBlockIso_inclusion j iota hsplit A ρ n τ, Iso.inv_hom_id_assoc]

def nativeBlockBaseChangeIso :
    (Over.pullback f).obj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))) ≅
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) ((ρ.pullback f).map (j.projector iota hsplit n τ)) :=
  (Over.pullback f).mapIso (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A ρ n τ) ≪≫
    l45BlockBaseChangeOverIso j iota hsplit A ρ f n τ ≪≫
      (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit (A.pullback f) (ρ.pullback f) n τ).symm

theorem nativeBlockBaseChangeIso_inclusion :
    (nativeBlockBaseChangeIso j iota hsplit A ρ f n τ).hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) ((ρ.pullback f).map (j.projector iota hsplit n τ)) =
    (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ))) := by
  change ((Over.pullback f).map (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A ρ n τ).hom ≫
    (l45BlockBaseChangeOverIso j iota hsplit A ρ f n τ).hom ≫
    (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit (A.pullback f) (ρ.pullback f) n τ).inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, nativeCMPointsBlockIso_inv_inclusion,
    l45BlockBaseChangeOverIso_inclusion]
  exact ((Over.pullback f).map_comp (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A ρ n τ).hom
    (CMPointsBlockComparison.l45BlockInclusion j iota hsplit A ρ n τ)).symm.trans
      (congrArg (fun a => (Over.pullback f).map a) (CMPointsBlockComparison.l45NativeBlockIso_inclusion j iota hsplit A ρ n τ))

theorem nativeBlockBaseChangeGroupIso_hom :
    (nativeBlockBaseChangeGroupIso j iota hsplit A ρ f n τ).hom.hom.hom =
      (nativeBlockBaseChangeIso j iota hsplit A ρ f n τ).hom := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange
