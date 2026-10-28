import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Family Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyFunctor

noncomputable section

/-!
The presheaf of flat locally finitely presented closed families in a fixed
ambient scheme over a base. The construction uses actual ideal pullback and
does not assert representability or fix a Hilbert polynomial.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P : Over S)

/-- The fixed ambient scheme after passage to a test scheme. -/
def embeddedFamilyAmbient (T : Over S) : Over T.left :=
  Over.mk (prod.fst : T ⨯ P ⟶ T).left

/-- The map of ambient schemes induced by a map of test schemes. -/
def embeddedFamilyAmbientMap {T U : Over S} (f : T ⟶ U) :
    (embeddedFamilyAmbient P T).left ⟶ (embeddedFamilyAmbient P U).left :=
  (prod.map f (𝟙 P)).left

theorem embeddedFamilyAmbient_isPullback {T U : Over S} (f : T ⟶ U) :
    IsPullback (embeddedFamilyAmbientMap P f) (embeddedFamilyAmbient P T).hom
      (embeddedFamilyAmbient P U).hom f.left :=
  (IsPullback.of_prod_fst_with_id f P).flip.map (Over.forget S)

/-- Embedded flat families form a presheaf by ordinary pullback of ideal sheaves. -/
def embeddedFlatFamilyFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Closed.Families.FlatClosedFamily (embeddedFamilyAmbient P T.unop)
  map f := ↾fun F => F.pullbackAlong (embeddedFamilyAmbientMap P f.unop) f.unop.left
    (embeddedFamilyAmbient_isPullback P f.unop)
  map_id T := by
    ext1
    ext1
    funext F
    apply Closed.Families.FlatClosedFamily.ext
    change F.ideal.comap (prod.map (𝟙 T.unop) (𝟙 P)).left = F.ideal
    rw [prod.map_id_id]
    exact F.ideal.comap_id
  map_comp f g := by
    ext1
    ext1
    funext F
    apply Closed.Families.FlatClosedFamily.ext
    change F.ideal.comap (prod.map (g.unop ≫ f.unop) (𝟙 P)).left =
      (F.ideal.comap (prod.map f.unop (𝟙 P)).left).comap (prod.map g.unop (𝟙 P)).left
    have he : (prod.map (g.unop ≫ f.unop) (𝟙 P)).left =
        (prod.map g.unop (𝟙 P)).left ≫ (prod.map f.unop (𝟙 P)).left :=
      congrArg Over.Hom.left (by
        simpa only [Category.id_comp] using (prod.map_map g.unop (𝟙 P) f.unop (𝟙 P)).symm)
    exact (congrArg (fun p => F.ideal.comap p) he).trans
      (F.ideal.comap_comp (prod.map g.unop (𝟙 P)).left (prod.map f.unop (𝟙 P)).left)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyFunctor
