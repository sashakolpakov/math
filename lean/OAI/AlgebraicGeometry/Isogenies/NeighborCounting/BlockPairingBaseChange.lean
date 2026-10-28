import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingInclusionSquares

/-! # Block Pairing Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockPairingBaseChange.Reduced

noncomputable section

/-! Canonical block pairings commute with the actual base-change maps
into native torsion; the blocks themselves are kept as the original schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local instance reducedBlockPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingPullbackRestriction
attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {S T : Scheme} [IsReduced S] [IsLocallyNoetherian S]
  [IsReduced T] [IsLocallyNoetherian T] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (f : T ⟶ S) (n : ℕ) (hn : 0 < n)
  (K L : Grp (Over S)) [IsCommMonObj K.X] [IsCommMonObj L.X]
  (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.scheme) n)
  (b : L ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.scheme) n)

local instance originalLeft_group :
    IsMonHom (show K.X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme n from a.hom.hom) := a.hom.isMonHom_hom

local instance originalRight_group :
    IsMonHom (show L.X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme n from b.hom.hom) := b.hom.isMonHom_hom

local instance changedLeft_group :
    IsMonHom (show ((Over.pullback f).mapGrp.obj K).X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.pullback f).scheme n from
      (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.scheme) n K a).hom.hom) :=
  (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.scheme) n K a).hom.isMonHom_hom

local instance changedRight_group :
    IsMonHom (show ((Over.pullback f).mapGrp.obj L).X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.pullback f).scheme n from
      (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.scheme) n L b).hom.hom) :=
  (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.scheme) n L b).hom.isMonHom_hom

theorem reducedBlockPairing_baseChange :
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing (A.pullback f) (D.pullback f)
      (pol.pullback f) n hn).restrict
        (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.scheme) n K a).hom.hom
        (TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.scheme) n L b).hom.hom =
      AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f K L
        ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn).restrict a.hom.hom b.hom.hom) := by
  rw [ReducedPairingBaseChange.reducedCanonicalPairing_baseChange]
  exact TorsionPairingPullbackRestriction.torsionPairingPullback_restrict f (Grp.mk A.scheme) n K a
    (Grp.mk A.scheme) L b (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockPairingBaseChange.Reduced
