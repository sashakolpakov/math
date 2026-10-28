import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Action Pairing Source Data -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData

noncomputable section

/-! Keep polarized source comparison and the two integral actions in
one coherent data index before specializing to a moduli lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local instance actionPairingPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {S T Q : Scheme} {dim level : ℕ} {δ : Fin dim → ℕ}
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E dim δ level S)
  (B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E dim δ level T) (f : Q ⟶ S) (g : Q ⟶ T)

structure ActionPairingSource where
  iso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.polarized.pullback f) (B.polarized.pullback g)
  groupIso : (Over.pullback f).mapGrp.obj (Grp.mk A.polarized.abelian.scheme) ≅
    (Over.pullback g).mapGrp.obj (Grp.mk B.polarized.abelian.scheme)
  map_eq : iso.abelian.hom = groupIso.hom.hom.hom

variable {A B f g}

abbrev ActionPairingSource.map (C : ActionPairingSource A B f g) := C.groupIso.hom.hom.hom

structure ActionPairingSource.BlockIso (C : ActionPairingSource A B f g)
    (n : ℕ) (t : NumberField.RingOfIntegers E) where
  iso : (Over.pullback f).mapGrp.obj (Lifted.GeometricBlockIso.nativeActionBlockGroup A.polarized.abelian A.action n t) ≅
    (Over.pullback g).mapGrp.obj (Lifted.GeometricBlockIso.nativeActionBlockGroup B.polarized.abelian B.action n t)
  inclusion : iso.hom.hom.hom ≫ (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (B.action.map t)) =
    (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (A.action.map t)) ≫ C.map

variable [IsReduced S] [IsLocallyNoetherian S] [IsReduced T] [IsLocallyNoetherian T]
  [IsReduced Q] [IsLocallyNoetherian Q]

def ActionPairingSource.blockPairingComparison (C : ActionPairingSource A B f g)
    (n : ℕ) (hn : 0 < n) (t u : NumberField.RingOfIntegers E) :=
  PLift.up (ActionBlockPairingIso.Polarized.polarizedActionBlockPairing_iso A.polarized B.polarized A.action B.action f g
    C.iso C.map C.map_eq n hn t u)

def ActionPairingSource.blockIsoPairing (C : ActionPairingSource A B f g)
    (n : ℕ) (hn : 0 < n) (t u : NumberField.RingOfIntegers E)
    (D : C.BlockIso n t) (H : C.BlockIso n u) :=
  PLift.up ((C.blockPairingComparison n hn t u).down
    D.iso.hom H.iso.hom D.inclusion H.inclusion)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionPairingSourceData
