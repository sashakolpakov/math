import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockPairingIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion

/-! # Action Block Pairing Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized

noncomputable section

/-! Canonical pairing transport for the original coefficient blocks of
integral actions, before specialization to an evaluated moduli lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local instance polarizedActionBlockPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActionBlockTorsionInclusion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockPairingIso
attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

def canonicalActionBlockPairing {O : Type} [CommRing O]
    {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A.abelian) (n : ℕ) (hn : 0 < n) (t u : O) :
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map t))
      (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map u)) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn).restrict
    (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (ρ.map t)))
    (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (ρ.map u)))

theorem polarizedActionBlockPairing_iso {O : Type} [CommRing O]
    {S T Q : Scheme} [IsReduced S] [IsLocallyNoetherian S]
    [IsReduced T] [IsLocallyNoetherian T] [IsReduced Q] [IsLocallyNoetherian Q]
    {dim level : ℕ} {δ : Fin dim → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ level S)
    (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ level T)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A.abelian) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B.abelian)
    (f : Q ⟶ S) (g : Q ⟶ T)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback g))
    (m : (A.pullback f).abelian.scheme ⟶ (B.pullback g).abelian.scheme)
    (hm : e.abelian.hom = m) (n : ℕ) (hn : 0 < n) (t u : O)
    (k : (Over.pullback f).mapGrp.obj (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map t))) ⟶
      (Over.pullback g).mapGrp.obj (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map t))))
    (r : (Over.pullback f).mapGrp.obj (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map u))) ⟶
      (Over.pullback g).mapGrp.obj (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map u))))
    (hk : k.hom.hom ≫ (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (σ.map t)) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map t)) ≫ m)
    (hr : r.hom.hom ≫ (Over.pullback g).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (σ.map u)) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (ρ.map u)) ≫ m) :
    (AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback g (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map t)))
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map u))) (canonicalActionBlockPairing B σ n hn t u)).restrict
        k.hom.hom r.hom.hom =
    AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map t)))
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map u))) (canonicalActionBlockPairing A ρ n hn t u) :=
  PolarizedBlockPairingIso.polarizedPulledBackBlockPairing_iso A B f g e m hm n hn
    (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map t))) (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map u)))
    (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map t))) (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (σ.map u)))
    (Intrinsic.ActionBlockTorsionInclusion.nativeActionBlockTorsionInclusion A.abelian ρ n t)
    (Intrinsic.ActionBlockTorsionInclusion.nativeActionBlockTorsionInclusion B.abelian σ n t)
    (Intrinsic.ActionBlockTorsionInclusion.nativeActionBlockTorsionInclusion A.abelian ρ n u)
    (Intrinsic.ActionBlockTorsionInclusion.nativeActionBlockTorsionInclusion B.abelian σ n u) k r hk hr

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionBlockPairingIso.Polarized
