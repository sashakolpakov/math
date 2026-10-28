import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

/-! # Adjunction Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComposition

/-! Coherence of the canonical adjunction isomorphisms used for constant coefficients. -/

open _root_.CategoryTheory

section Associativity

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ C} {I : C ⥤ B} {J : C ⥤ D} {K : D ⥤ C}

theorem comp_assoc (a : F ⊣ G) (b : H ⊣ I) (c : J ⊣ K) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext X
  rw [Adjunction.comp_unit_app (a.comp b) c X, Adjunction.comp_unit_app a (b.comp c) X]
  change (a.comp b).unit.app X ≫ G.map (I.map (c.unit.app (H.obj (F.obj X)))) =
    a.unit.app X ≫ G.map ((b.comp c).unit.app (F.obj X))
  rw [Adjunction.comp_unit_app a b X, Adjunction.comp_unit_app b c (F.obj X),
    G.map_comp, Category.assoc]

end Associativity

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {F F' : A ⥤ B} {G : B ⥤ A} {H H' : B ⥤ C} {I : C ⥤ B}

theorem leftAdjointUniq_whiskerLeft (a : F ⊣ G) (b : H ⊣ I) (b' : H' ⊣ I) (X : A) :
    ((a.comp b).leftAdjointUniq (a.comp b')).hom.app X =
      (b.leftAdjointUniq b').hom.app (F.obj X) := by
  apply ((a.comp b).homEquiv X (H'.obj (F.obj X))).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.comp_homEquiv]
  change (a.comp b').unit.app X =
    a.homEquiv X _ (b.homEquiv (F.obj X) _ ((b.leftAdjointUniq b').hom.app (F.obj X)))
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, a.homEquiv_unit, Adjunction.comp_unit_app]

theorem leftAdjointUniq_whiskerRight (a : F ⊣ G) (a' : F' ⊣ G) (b : H ⊣ I) (X : A) :
    ((a.comp b).leftAdjointUniq (a'.comp b)).hom.app X =
      H.map ((a.leftAdjointUniq a').hom.app X) := by
  apply ((a.comp b).homEquiv X (H.obj (F'.obj X))).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have h := AdjunctionComplexUniqueness.comp_homEquiv_map_comp a b ((a.leftAdjointUniq a').hom.app X) (𝟙 (H.obj (F'.obj X)))
  erw [Category.comp_id, b.homEquiv_id, Adjunction.homEquiv_leftAdjointUniq_hom_app] at h
  exact (Adjunction.comp_unit_app a' b X).trans h.symm

end OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComposition
