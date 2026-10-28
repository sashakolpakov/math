import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeValues
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks

/-! # Torsion Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction

noncomputable section

/-!
An original torsion pairing induces a pairing on the actual torsion of
each base-changed source. The canonical kernel comparison preserves
perfection and the original all-test pairing values.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {S T : Scheme.{u}} (f : T ⟶ S) (G H : Grp (Over S))
  [IsCommMonObj G.X] [IsCommMonObj H.X] (n : ℕ)
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme G.X n) (B := Torsion.Groups.Construction.nativeTorsionScheme H.X n)
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

def nativeTorsionPairingPullback :
    IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback f).mapGrp.obj G) n).X)
      (B := (Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback f).mapGrp.obj H) n).X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T).X) :=
  (PairingBaseChange.Construction.nativePairingPullback f (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (Torsion.SheafComparison.Construction.kernelTorsionGroup H n) e).restrict
    (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv.hom.hom (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).inv.hom.hom

theorem nativeTorsionPairingPullback_isPerfect (he : e.toSheafPairing.IsPerfect) :
    (nativeTorsionPairingPullback f G H n e).toSheafPairing.IsPerfect := by
  apply (PairingBaseChange.Construction.nativePairingPullback f (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (Torsion.SheafComparison.Construction.kernelTorsionGroup H n) e).restrict_isPerfect
    (PairingBaseChange.Construction.nativePairingPullback_isPerfect f (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (Torsion.SheafComparison.Construction.kernelTorsionGroup H n) e he)
    (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv.hom.hom (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).hom.hom.hom
    (congrArg (fun k => (Grp.forget (Over T)).map k) (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv_hom_id)
    (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).inv.hom.hom (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).hom.hom.hom
    (congrArg (fun k => (Grp.forget (Over T)).map k) (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).inv_hom_id)
  intro U x y
  have hG := congrArg (fun k => (Grp.forget (Over T)).map k) (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).hom_inv_id
  have hH := congrArg (fun k => (Grp.forget (Over T)).map k) (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).hom_inv_id
  change (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).hom.hom.hom ≫
    (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv.hom.hom = 𝟙 _ at hG
  change (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).hom.hom.hom ≫
    (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).inv.hom.hom = 𝟙 _ at hH
  rw [hG, hH, Category.comp_id, Category.comp_id]

theorem nativeTorsionPairingPullback_value (U : Over T)
    (x : U ⟶ (Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback f).mapGrp.obj G) n).X)
    (y : U ⟶ (Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback f).mapGrp.obj H) n).X) :
    (nativeTorsionPairingPullback f G H n e).pairValue x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U
        (e.pairValue
          ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) U).symm
            (x ≫ (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f G n).inv.hom.hom))
          ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (Torsion.SheafComparison.Construction.kernelTorsionGroup H n) U).symm
            (y ≫ (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso f H n).inv.hom.hom))) := by
  exact (Annihilator.Construction.SchemeBicharacter.restrict_pairValue _ _ _ x y).trans
    (PairingBaseChangeValues.Construction.nativePairingPullback_native_value f (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (Torsion.SheafComparison.Construction.kernelTorsionGroup H n) e U _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction
