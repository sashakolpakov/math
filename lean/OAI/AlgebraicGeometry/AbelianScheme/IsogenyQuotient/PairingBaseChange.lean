import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Pairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.PairingBaseChange

/-! # Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction

noncomputable section

/-!
The actual base change of a scheme pairing is obtained from the canonical
base-changed sheaf pairing and the represented group comparisons. Its
perfection is a conclusion for every base morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (G H : Grp (Over S))
  [IsCommMonObj G.X] [IsCommMonObj H.X]

local instance pulledbackGroup_commutative (J : Grp (Over S)) [IsCommMonObj J.X] :
    IsCommMonObj ((Over.pullback f).mapGrp.obj J).X :=
  Functor.isCommMonObj_obj (F := Over.pullback f) (M := J.X)

def nativePairingPullbackSheaf
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb T ((Over.pullback f).mapGrp.obj G))
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb T ((Over.pullback f).mapGrp.obj H)) :=
  (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f e.toSheafPairing).restrict
    (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbBaseChangeIso f G).inv (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbBaseChangeIso f H).inv

def nativePairingPullback
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    Annihilator.Construction.SchemeBicharacter (A := ((Over.pullback f).mapGrp.obj G).X)
      (B := ((Over.pullback f).mapGrp.obj H).X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T).X) :=
  Sheaf.Pairing.Construction.sheafPairingToScheme (nativePairingPullbackSheaf f G H e)

theorem nativePairingPullback_toSheaf
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    (nativePairingPullback f G H e).toSheafPairing = nativePairingPullbackSheaf f G H e :=
  Sheaf.Pairing.Construction.sheafPairingToScheme_toSheaf (nativePairingPullbackSheaf f G H e)

theorem nativePairingPullback_isPerfect
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect) : (nativePairingPullback f G H e).toSheafPairing.IsPerfect := by
  rw [nativePairingPullback_toSheaf]
  exact Sheaf.PairingBaseChange.Construction.sheafPairing_restrict_isPerfect_of_iso _
    (Sheaf.PairingBaseChange.Construction.sheafPairing_baseChange_isPerfect f e.toSheafPairing he) _ _

theorem representedPairingBaseChangeIso_inv_value
    (U : Over T) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbBaseChangeIso f G).inv.hom.app (.op U) (ULift.up x) =
      ULift.up ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x) := rfl

theorem nativePairingPullback_value
    (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (U : Over T) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X)
    (y : U ⟶ ((Over.pullback f).mapGrp.obj H).X) :
    ULift.up ((nativePairingPullback f G H e).pairValue x y) =
      (CartierDuality.SheafBaseChange.Construction.Schemes.multiplicativeFppfAbBaseChangeIso f).hom.hom.app (.op U)
        (ULift.up (e.pairValue ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x)
          ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H U).symm y))) := by
  let ep := CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f e.toSheafPairing
  let ix := (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbBaseChangeIso f G).inv.hom.app (.op U) (ULift.up x)
  let iy := (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbBaseChangeIso f H).inv.hom.app (.op U) (ULift.up y)
  have hvalue := CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbBaseChangeIso f H).inv U
    (ep.leftAdjoint.hom.app (.op U) ix) (ULift.up y)
  have hn := (nativePairingPullback f G H e).toSheafPairing_value U x y
  rw [nativePairingPullback_toSheaf] at hn
  exact hn.symm.trans (hvalue.trans
    ((ep.adjoint_value U ix iy).symm.trans
      ((CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing_value f e.toSheafPairing U ix iy).trans
        (congrArg ((CartierDuality.SheafBaseChange.Construction.Schemes.multiplicativeFppfAbBaseChangeIso f).hom.hom.app (.op U))
          (e.toSheafPairing_rightValue ((Over.map f).obj U)
            ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x) ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H U).symm y))))))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction
