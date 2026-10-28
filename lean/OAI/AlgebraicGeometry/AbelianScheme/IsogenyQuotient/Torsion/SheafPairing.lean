import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.PairingBaseChange

/-! # Sheaf Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction

noncomputable section

/-!
A pairing on CartierDuality's actual torsion kernels gives a unique pairing on the
native IsogenyQuotient torsion schemes. Perfection and every original pairing value
are transported through the canonical kernel comparisons.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
  (n : ℕ)
  (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n)
    (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n))

def torsionSheafPairingToNative : Annihilator.Construction.SchemeBicharacter
    (A := Groups.Construction.nativeTorsionScheme G.X n) (B := Groups.Construction.nativeTorsionScheme K.X n)
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Sheaf.Pairing.Construction.sheafPairingToScheme (e.restrict (SheafComparison.Construction.kernelTorsionSheafIso G n).hom (SheafComparison.Construction.kernelTorsionSheafIso K n).hom)

theorem torsionSheafPairingToNative_toSheaf :
    (torsionSheafPairingToNative G K n e).toSheafPairing =
      e.restrict (SheafComparison.Construction.kernelTorsionSheafIso G n).hom (SheafComparison.Construction.kernelTorsionSheafIso K n).hom :=
  Sheaf.Pairing.Construction.sheafPairingToScheme_toSheaf _

theorem torsionSheafPairingToNative_isPerfect (he : e.IsPerfect) :
    (torsionSheafPairingToNative G K n e).toSheafPairing.IsPerfect := by
  rw [torsionSheafPairingToNative_toSheaf]
  exact @Sheaf.PairingBaseChange.Construction.sheafPairing_restrict_isPerfect_of_iso S _ _ _ _ e he
    (SheafComparison.Construction.kernelTorsionSheafIso G n).hom (SheafComparison.Construction.kernelTorsionSheafIso K n).hom
    (SheafComparison.Construction.kernelTorsionSheafIso G n).isIso_hom (SheafComparison.Construction.kernelTorsionSheafIso K n).isIso_hom

theorem torsionSheafPairingToNative_value
    (T : Over S) (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n) (y : T ⟶ Groups.Construction.nativeTorsionScheme K.X n) :
    ULift.up ((torsionSheafPairingToNative G K n e).pairValue x y) =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n) T
        (e.leftAdjoint.hom.app (.op T) ((SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)))
        ((SheafComparison.Construction.kernelTorsionSheafIso K n).hom.hom.app (.op T) (ULift.up y)) := by
  have hv := (torsionSheafPairingToNative G K n e).toSheafPairing_value T x y
  rw [torsionSheafPairingToNative_toSheaf] at hv
  exact hv.symm.trans
    (CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value (SheafComparison.Construction.kernelTorsionSheafIso K n).hom T
      (e.leftAdjoint.hom.app (.op T) ((SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)))
      (ULift.up y))

theorem torsionSheafPairingToNative_rightValue
    (T : Over S) (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n) (y : T ⟶ Groups.Construction.nativeTorsionScheme K.X n) :
    ULift.up ((torsionSheafPairingToNative G K n e).pairValue x y) =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) T
        (e.rightAdjoint.hom.app (.op T) ((SheafComparison.Construction.kernelTorsionSheafIso K n).hom.hom.app (.op T) (ULift.up y)))
        ((SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)) :=
  (torsionSheafPairingToNative_value G K n e T x y).trans (e.adjoint_value T _ _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafPairing.Construction
