import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation

/-! # Sheaf Pairing Character Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingCharacterPoints.Construction

noncomputable section

/-! Evaluation of an inverse character-line map on a represented
character point recovers the original character value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes

theorem sheafPairing_characterPoint {S : Scheme} {K G R H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : K ≅ G) (c : R ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf K) (a : CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G ≅ H)
    (t : R ⟶ H)
    (h : c.hom ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map e.inv.op ≫ a.hom = t)
    (T : Over S) (d : R.obj.obj (.op T)) (x : K.obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (a.inv.hom.app (.op T) (t.hom.app (.op T) d))
        (e.hom.hom.app (.op T) x) =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue K T (c.hom.hom.app (.op T) d) x := by
  have ha : t ≫ a.inv = c.hom ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map e.inv.op := by
    apply a.comp_inv_eq.mpr
    exact ((Category.assoc c.hom ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map e.inv.op) a.hom).trans h).symm
  have hd := congrArg (fun z : R ⟶ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G => z.hom.app (.op T) d) ha
  have he : e.inv.hom.app (.op T) (e.hom.hom.app (.op T) x) = x :=
    congrArg (fun z : K ⟶ K => z.hom.app (.op T) x) e.hom_inv_id
  exact (congrArg (fun χ => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T χ (e.hom.hom.app (.op T) x)) hd).trans
    ((CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value e.inv T (c.hom.hom.app (.op T) d)
      (e.hom.hom.app (.op T) x)).trans
      (congrArg (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue K T (c.hom.hom.app (.op T) d)) he))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingCharacterPoints.Construction
