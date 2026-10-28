import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Change Of Left Adjoint -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ChangeOfLeftAdjoint.MateChange

noncomputable section

/-! Inverse mates respect the canonical isomorphisms between left adjoints of the same right adjoint. -/
open _root_.CategoryTheory
variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L L' : C ⥤ D} {R : D ⥤ C} {E E' : C' ⥤ D'} {Q : D' ⥤ C'}
    {F : C ⥤ C'} {G : D ⥤ D'}

def leftMap (a : L ⊣ R) (b : E ⊣ Q) (t : R ⋙ F ⟶ G ⋙ Q) : F ⋙ E ⟶ L ⋙ G :=
  ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t)).natTrans

theorem normalization (a : L ⊣ R) (b : E ⊣ Q) (t : R ⋙ F ⟶ G ⋙ Q) (X : C) :
    b.homEquiv _ _ ((leftMap a b t).app X) = F.map (a.unit.app X) ≫ t.app (L.obj X) :=
  (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ t) X).symm

theorem leftAdjointUniq_compatibility (a : L ⊣ R) (a' : L' ⊣ R)
    (b : E ⊣ Q) (b' : E' ⊣ Q) (t : R ⋙ F ⟶ G ⋙ Q) (X : C) :
    (b.leftAdjointUniq b').hom.app (F.obj X) ≫ (leftMap a' b' t).app X =
      (leftMap a b t).app X ≫ G.map ((a.leftAdjointUniq a').hom.app X) := by
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change b'.homEquiv _ _ ((leftMap a' b' t).app X) =
    b.homEquiv _ _ ((leftMap a b t).app X ≫ G.map ((a.leftAdjointUniq a').hom.app X))
  rw [normalization, Adjunction.homEquiv_naturality_right, normalization]
  let α := (a.leftAdjointUniq a').hom.app X
  have hn : F.map (R.map α) ≫ t.app (L'.obj X) = t.app (L.obj X) ≫ Q.map (G.map α) :=
    t.naturality α
  calc
    F.map (a'.unit.app X) ≫ t.app (L'.obj X) =
        F.map (a.unit.app X ≫ R.map α) ≫ t.app (L'.obj X) :=
      congrArg (fun z => F.map z ≫ t.app (L'.obj X))
        (a.unit_leftAdjointUniq_hom_app a' X).symm
    _ = _ := by rw [F.map_comp, Category.assoc, hn, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ChangeOfLeftAdjoint.MateChange
