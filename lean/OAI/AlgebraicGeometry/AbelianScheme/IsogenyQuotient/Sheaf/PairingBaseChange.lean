import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AnnihilatorBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks

/-! # Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.PairingBaseChange.Construction

noncomputable section

/-!
Both actual adjoints of the base-changed pairing are the base changes
of the original adjoints. Consequently perfection is preserved by every
base change and by transport along isomorphisms of the two source sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AnnihilatorBaseChange.Construction.Schemes

universe u

theorem sheafPairing_baseChange_leftAdjoint
    {S T : Scheme.{u}} (f : T ⟶ S) {G K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) :
    (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f e).leftAdjoint =
      (CartierDuality.SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map e.leftAdjoint ≫ (CartierDuality.SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f K).hom := by
  apply CartierDuality.SheafEvaluation.Construction.Schemes.sheafDualHom_ext
  intro U x y
  exact ((CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f e).adjoint_value U x y).symm.trans
    ((CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing_value f e U x y).trans
      ((congrArg ((CartierDuality.SheafBaseChange.Construction.Schemes.multiplicativeFppfAbBaseChangeIso f).hom.hom.app (.op U))
        (e.adjoint_value ((Over.map f).obj U) x y)).trans
          (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.sheafDualBaseChangeIso_value f K U
            (e.leftAdjoint.hom.app (.op ((Over.map f).obj U)) x) y).symm))

theorem sheafPairing_baseChange_isPerfect
    {S T : Scheme.{u}} (f : T ⟶ S) {G K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (he : e.IsPerfect) : (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f e).IsPerfect := by
  let := he.1
  let := he.2
  have hl : IsIso ((CartierDuality.SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map e.leftAdjoint ≫ (CartierDuality.SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f K).hom) :=
    inferInstance
  have hr : IsIso ((CartierDuality.SheafBaseChange.Construction.Schemes.baseChangeFppfAb f).map e.rightAdjoint ≫ (CartierDuality.SheafBaseChange.Construction.Schemes.sheafDualBaseChangeIso f G).hom) :=
    inferInstance
  exact ⟨(sheafPairing_baseChange_leftAdjoint f e).symm ▸ hl,
    (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing_rightAdjoint f e).symm ▸ hr⟩

theorem sheafPairing_restrict_isPerfect_of_iso
    {S : Scheme.{u}} {G K G' K' : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (he : e.IsPerfect)
    (i : G' ⟶ G) (j : K' ⟶ K) [IsIso i] [IsIso j] : (e.restrict i j).IsPerfect := by
  let el : G ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf K := @asIso _ _ _ _ e.leftAdjoint he.1
  let er : K ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G := @asIso _ _ _ _ e.rightAdjoint he.2
  have hl : IsIso (i ≫ e.leftAdjoint ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map j.op) :=
    (asIso i ≪≫ el ≪≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (asIso j).op).isIso_hom
  have hr : IsIso (j ≫ e.rightAdjoint ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op) :=
    (asIso j ≪≫ er ≪≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (asIso i).op).isIso_hom
  exact ⟨hl, (e.restrict_rightAdjoint i j).symm ▸ hr⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.PairingBaseChange.Construction
