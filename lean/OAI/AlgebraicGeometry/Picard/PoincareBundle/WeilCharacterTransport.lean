import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation

/-! # Weil Character Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilCharacterTransport

noncomputable section

/-! Actual character evaluation is preserved by the Cartier and torsion comparison isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes

private theorem iso_cancel {V : Type*} [Category* V] {X Y Z : V} (a : X ≅ Y) (b : Y ≅ Z) :
    b.hom ≫ (a ≪≫ b).inv ≫ a.hom = 𝟙 Y := by
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id]

variable {S : Scheme.{u}} {G G' H : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
  (i : G ≅ G') (j : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G ≅ H)

/-- The character obtained by inverting Cartier-Picard descent evaluates as the original character. -/
theorem value (T : Over S) (χ : (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.obj (.op T)) (x : G.obj.obj (.op T)) :
    AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G' T
      (((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso i.op ≪≫ j).inv.hom.app (.op T)
        (j.hom.hom.app (.op T) χ))
      (i.hom.hom.app (.op T) x) = AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T χ x := by
  refine (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value i.hom T _ x).symm.trans ?_
  have h : j.hom ≫ ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso i.op ≪≫ j).inv ≫
      ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso i.op).hom = 𝟙 (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) :=
    iso_cancel ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso i.op) j
  have hp := congrArg (fun m : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G ⟶ AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G => m.hom.app (.op T) χ) h
  exact congrArg (fun c => AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T c x) hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilCharacterTransport
