import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! # Adjunction Complex Uniqueness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

section

/-! Explicit normalization of comparison squares under the actual adjunctions. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}

theorem comp_homEquiv_map_comp (a : F ⊣ G) (b : H ⊣ I)
    {X : C} {Y : D} {Z : E} (f : F.obj X ⟶ Y) (g : H.obj Y ⟶ Z) :
    (a.comp b).homEquiv X Z (H.map f ≫ g) =
      a.homEquiv X Y f ≫ G.map (b.homEquiv Y Z g) := by
  rw [Adjunction.comp_homEquiv]
  change a.homEquiv X (I.obj Z) (b.homEquiv (F.obj X) Z (H.map f ≫ g)) = _
  rw [b.homEquiv_naturality_left f g, a.homEquiv_naturality_right]

theorem leftAdjointUniq_homEquiv {F' : C ⥤ D} (a : F ⊣ G) (b : F' ⊣ G)
    {X : C} {Y : D} (g : F'.obj X ⟶ Y) :
    a.homEquiv X Y ((a.leftAdjointUniq b).hom.app X ≫ g) = b.homEquiv X Y g := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    b.homEquiv_unit]

theorem leftAdjointUniq_inv_homEquiv {F' : C ⥤ D} (a : F ⊣ G) (b : F' ⊣ G)
    {X : C} {Y : D} (g : F.obj X ⟶ Y) :
    b.homEquiv X Y ((a.leftAdjointUniq b).inv.app X ≫ g) = a.homEquiv X Y g :=
  leftAdjointUniq_homEquiv b a g

end

/-! The canonical adjunction comparison on complexes is degreewise the sheaf comparison. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  {F F' : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
  [F.Additive] [F'.Additive] [G.Additive] [H.Additive] [I.Additive]
  {ι : Type*} (c : ComplexShape ι)

theorem onComplexes_comp (a : F ⊣ G) (b : H ⊣ I) :
    Complex.Adjunction.onComplexes (a.comp b) c =
      (Complex.Adjunction.onComplexes a c).comp (Complex.Adjunction.onComplexes b c) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext i
  change (a.comp b).unit.app (K.X i) =
    (((Complex.Adjunction.onComplexes a c).comp (Complex.Adjunction.onComplexes b c)).unit.app K).f i
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rfl

theorem onComplexes_leftAdjointUniq (a : F ⊣ G) (b : F' ⊣ G)
    (K : HomologicalComplex C c) :
    ((Complex.Adjunction.onComplexes a c).leftAdjointUniq
      (Complex.Adjunction.onComplexes b c)).hom.app K =
    (NatTrans.mapHomologicalComplex (a.leftAdjointUniq b).hom c).app K := by
  let ac := Complex.Adjunction.onComplexes a c
  let bc := Complex.Adjunction.onComplexes b c
  apply (ac.homEquiv K ((F'.mapHomologicalComplex c).obj K)).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app ac bc K]

end OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness
