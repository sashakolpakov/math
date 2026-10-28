import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockPairingBaseChange

/-! # Polarized Block Pairing Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockPairingIso

noncomputable section

/-! Actual polarized isomorphisms preserve canonical pairings on the
original embedded blocks. The ambient inclusion equations determine
the torsion equations; the normalized Poincare data determines the pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

local instance polarizedBlockPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingInclusionSquares
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingPullbackRestriction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockPairingBaseChange.Reduced
attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

local instance nativeTorsionArrow_group {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ) (K : Grp (Over S))
    (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.scheme) n) :
    IsMonHom (show K.X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme n from a.hom.hom) := a.hom.isMonHom_hom

theorem polarizedBlockPairing_iso {S : Scheme} [IsReduced S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) (n : ℕ) (hn : 0 < n)
    (K L U V : Grp (Over S))
    (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.abelian.scheme) n)
    (b : L ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk B.abelian.scheme) n)
    (c : U ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.abelian.scheme) n)
    (d : V ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk B.abelian.scheme) n)
    (k : K ⟶ L) (r : U ⟶ V)
    (hk : k.hom.hom ≫ b.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B.abelian.scheme n =
      a.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n ≫ e.abelian.hom)
    (hr : r.hom.hom ≫ d.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B.abelian.scheme n =
      c.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n ≫ e.abelian.hom) :
    ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing B.abelian B.dual B.polarization n hn).restrict
      b.hom.hom d.hom.hom).restrict k.hom.hom r.hom.hom =
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn).restrict
      a.hom.hom c.hom.hom :=
  TorsionPairingInclusionSquares.torsion_pairing_restriction_square n e.abelian.hom a.hom.hom b.hom.hom
    c.hom.hom d.hom.hom k.hom.hom r.hom.hom _ _ hk hr
    (PolarizedIsoCanonicalPairing.polarizedIso_canonical_pairing e n hn)

theorem polarizedPulledBackBlockPairing_iso
    {S T Q : Scheme} [IsReduced S] [IsLocallyNoetherian S]
    [IsReduced T] [IsLocallyNoetherian T] [IsReduced Q] [IsLocallyNoetherian Q]
    {dim level : ℕ} {δ : Fin dim → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ level S)
    (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ level T) (f : Q ⟶ S) (g : Q ⟶ T)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback g))
    (m : (A.pullback f).abelian.scheme ⟶ (B.pullback g).abelian.scheme)
    (hm : e.abelian.hom = m) (n : ℕ) (hn : 0 < n)
    (K U : Grp (Over S)) (L V : Grp (Over T))
    [IsCommMonObj K.X] [IsCommMonObj U.X] [IsCommMonObj L.X] [IsCommMonObj V.X]
    (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.abelian.scheme) n)
    (b : L ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk B.abelian.scheme) n)
    (c : U ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.abelian.scheme) n)
    (d : V ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk B.abelian.scheme) n)
    (k : (Over.pullback f).mapGrp.obj K ⟶ (Over.pullback g).mapGrp.obj L)
    (r : (Over.pullback f).mapGrp.obj U ⟶ (Over.pullback g).mapGrp.obj V)
    (hk : k.hom.hom ≫ (Over.pullback g).map (b.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B.abelian.scheme n) =
      (Over.pullback f).map (a.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n) ≫ m)
    (hr : r.hom.hom ≫ (Over.pullback g).map (d.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B.abelian.scheme n) =
      (Over.pullback f).map (c.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n) ≫ m) :
    (AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback g L V
      ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing B.abelian B.dual B.polarization n hn).restrict
        b.hom.hom d.hom.hom)).restrict k.hom.hom r.hom.hom =
    AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f K U
      ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn).restrict
        a.hom.hom c.hom.hom) := by
  let a' := TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.abelian.scheme) n K a
  let b' := TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap g (Grp.mk B.abelian.scheme) n L b
  let c' := TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap f (Grp.mk A.abelian.scheme) n U c
  let d' := TorsionPairingPullbackRestriction.torsionPairingBaseChangeMap g (Grp.mk B.abelian.scheme) n V d
  have ha := TorsionPairingInclusionSquares.torsionPairingBaseChangeMap_inclusion f (Grp.mk A.abelian.scheme) n K a
  have hb := TorsionPairingInclusionSquares.torsionPairingBaseChangeMap_inclusion g (Grp.mk B.abelian.scheme) n L b
  have hc := TorsionPairingInclusionSquares.torsionPairingBaseChangeMap_inclusion f (Grp.mk A.abelian.scheme) n U c
  have hd := TorsionPairingInclusionSquares.torsionPairingBaseChangeMap_inclusion g (Grp.mk B.abelian.scheme) n V d
  have hk₀ := hk.trans (congrArg (fun z =>
    (Over.pullback f).map (a.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n) ≫ z) hm.symm)
  have hr₀ := hr.trans (congrArg (fun z =>
    (Over.pullback f).map (c.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n) ≫ z) hm.symm)
  have hk' : k.hom.hom ≫ b'.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (B.pullback g).abelian.scheme n =
      a'.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback f).abelian.scheme n ≫ e.abelian.hom :=
    (congrArg (fun z => k.hom.hom ≫ z) hb).trans
      (hk₀.trans ((congrArg (fun z => z ≫ e.abelian.hom) ha.symm).trans (Category.assoc _ _ _)))
  have hr' : r.hom.hom ≫ d'.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (B.pullback g).abelian.scheme n =
      c'.hom.hom ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback f).abelian.scheme n ≫ e.abelian.hom :=
    (congrArg (fun z => r.hom.hom ≫ z) hd).trans
      (hr₀.trans ((congrArg (fun z => z ≫ e.abelian.hom) hc.symm).trans (Category.assoc _ _ _)))
  have h := polarizedBlockPairing_iso e n hn _ _ _ _ a' b' c' d' k r hk' hr'
  have hA := BlockPairingBaseChange.Reduced.reducedBlockPairing_baseChange A.abelian A.dual A.polarization f n hn K U a c
  have hB := BlockPairingBaseChange.Reduced.reducedBlockPairing_baseChange B.abelian B.dual B.polarization g n hn L V b d
  exact (congrArg (fun p => p.restrict k.hom.hom r.hom.hom) hB.symm).trans (h.trans hA)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockPairingIso
