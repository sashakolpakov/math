import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PairingPullbackRestriction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange

/-! # Torsion Pairing Pullback Restriction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingPullbackRestriction

noncomputable section

/-! The actual torsion base-change isomorphism identifies the pulled-back
original block pairing with restriction of the changed-source pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PairingPullbackRestriction
attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X]
  (n : ℕ) (K : Grp (Over S)) (a : K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n)

def torsionPairingBaseChangeMap :
    (Over.pullback f).mapGrp.obj K ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback f).mapGrp.obj G) n :=
  (Over.pullback f).mapGrp.map a ≫ (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).hom

theorem torsionPairingBaseChangeMap_inverse :
    (torsionPairingBaseChangeMap f G n K a).hom.hom ≫
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv.hom.hom =
        ((Over.pullback f).mapGrp.map a).hom.hom :=
  congrArg (fun z => z.hom.hom)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (Over.pullback f).mapGrp.map a ≫ z)
        (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).hom_inv_id).trans (Category.comp_id _)))

variable (H : Grp (Over S)) [IsCommMonObj H.X] (L : Grp (Over S))
  [IsCommMonObj K.X] [IsCommMonObj L.X] (b : L ⟶ AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup H n)
  (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n).X) (B := (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup H n).X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem torsionPairingPullback_restrict :
    (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback f G H n e).restrict
        (torsionPairingBaseChangeMap f G n K a).hom.hom
        (torsionPairingBaseChangeMap f H n L b).hom.hom =
      AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f K L (e.restrict a.hom.hom b.hom.hom) := by
  apply AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro Q x y
  let ep := AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback f (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup H n) e
  have hx : (x ≫ (torsionPairingBaseChangeMap f G n K a).hom.hom) ≫
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv.hom.hom =
        x ≫ ((Over.pullback f).mapGrp.map a).hom.hom :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => x ≫ z) (torsionPairingBaseChangeMap_inverse f G n K a))
  have hy : (y ≫ (torsionPairingBaseChangeMap f H n L b).hom.hom) ≫
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).inv.hom.hom =
        y ≫ ((Over.pullback f).mapGrp.map b).hom.hom :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => y ≫ z) (torsionPairingBaseChangeMap_inverse f H n L b))
  have hp := congrArg (fun p => p.pairValue x y)
    (PairingPullbackRestriction.pairingPullback_restrict f (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup H n) K L a b e)
  exact (AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue _ _ _ x y).trans
    ((AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue ep _ _ _ _).trans
      ((congrArg₂ ep.pairValue hx hy).trans
        ((AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue ep _ _ x y).symm.trans hp.symm)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TorsionPairingPullbackRestriction
