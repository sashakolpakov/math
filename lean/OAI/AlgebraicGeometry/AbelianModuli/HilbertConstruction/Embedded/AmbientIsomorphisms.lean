import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.ForgetfulMaps

/-! # Ambient Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Changes of ambient coordinates act on embedded polarized families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P Q R : Over S} {T U : Over S}

/-- An ambient isomorphism induces an isomorphism over each test scheme. -/
def AmbientIsomorphisms.embeddedAmbientIso (e : P ≅ Q) (T : Over S) :
    FamilyFunctor.embeddedFamilyAmbient P T ≅ FamilyFunctor.embeddedFamilyAmbient Q T :=
  Over.isoMk ((Over.forget S).mapIso (prod.mapIso (Iso.refl T) e))
    (congrArg Over.Hom.left ((prod.map_fst (𝟙 T) e.hom).trans (Category.comp_id _)))

/-- Ambient coordinate changes commute with base change of the test scheme. -/
theorem AmbientIsomorphisms.embeddedAmbientIso_naturality (e : P ≅ Q) (f : T ⟶ U) :
    (AmbientIsomorphisms.embeddedAmbientIso e T).hom.left ≫ FamilyFunctor.embeddedFamilyAmbientMap Q f =
      FamilyFunctor.embeddedFamilyAmbientMap P f ≫ (AmbientIsomorphisms.embeddedAmbientIso e U).hom.left := by
  change (prod.map (𝟙 T) e.hom).left ≫ (prod.map f (𝟙 Q)).left =
    (prod.map f (𝟙 P)).left ≫ (prod.map (𝟙 U) e.hom).left
  have he : prod.map (𝟙 T) e.hom ≫ prod.map f (𝟙 Q) =
      prod.map f (𝟙 P) ≫ prod.map (𝟙 U) e.hom := by
    simp only [prod.map_map, Category.id_comp, Category.comp_id]
  exact congrArg Over.Hom.left he

theorem AmbientIsomorphisms.embeddedAmbientIso_refl (P : Over S) (T : Over S) :
    (AmbientIsomorphisms.embeddedAmbientIso (Iso.refl P) T).hom = 𝟙 (FamilyFunctor.embeddedFamilyAmbient P T) := by
  apply Over.OverMorphism.ext
  have he := congrArg (fun f : T ⨯ P ⟶ T ⨯ P => f.left)
    (prod.map_id_id : prod.map (𝟙 T) (𝟙 P) = 𝟙 (T ⨯ P))
  exact he

theorem AmbientIsomorphisms.embeddedAmbientIso_trans (e : P ≅ Q) (h : Q ≅ R) (T : Over S) :
    (AmbientIsomorphisms.embeddedAmbientIso (e ≪≫ h) T).hom =
      (AmbientIsomorphisms.embeddedAmbientIso e T).hom ≫ (AmbientIsomorphisms.embeddedAmbientIso h T).hom := by
  apply Over.OverMorphism.ext
  have he : prod.map (𝟙 T) (e.hom ≫ h.hom) =
      prod.map (𝟙 T) e.hom ≫ prod.map (𝟙 T) h.hom := by
    simpa only [Category.id_comp] using (prod.map_map (𝟙 T) e.hom (𝟙 T) h.hom).symm
  have hleft := congrArg (fun f : T ⨯ P ⟶ T ⨯ R => f.left) he
  exact hleft

variable {g N : ℕ} {δ : Fin g → ℕ}

/-- Change ambient coordinates while retaining all polarized moduli data. -/
def PolarizedObjects.EmbeddedPolarizedObject.changeAmbient (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N T)
    (e : P ≅ Q) : PolarizedObjects.EmbeddedPolarizedObject Q g δ N T where
  object := A.object
  embedding := A.embedding ≫ (AmbientIsomorphisms.embeddedAmbientIso e T).hom
  closedImmersion := by
    have : IsIso (AmbientIsomorphisms.embeddedAmbientIso e T).hom.left :=
      inferInstanceAs (IsIso ((Over.forget T.left).map (AmbientIsomorphisms.embeddedAmbientIso e T).hom))
    exact @IsClosedImmersion.comp _ _ _ A.embedding.left (AmbientIsomorphisms.embeddedAmbientIso e T).hom.left
      inferInstance inferInstance

/-- Isomorphisms of embedded objects persist after changing ambient coordinates. -/
def PolarizedIsomorphisms.EmbeddedLevelIso.changeAmbient {A B : PolarizedObjects.EmbeddedPolarizedObject P g δ N T}
    (h : PolarizedIsomorphisms.EmbeddedLevelIso A B) (e : P ≅ Q) :
    PolarizedIsomorphisms.EmbeddedLevelIso (A.changeAmbient e) (B.changeAmbient e) where
  iso := h.iso
  embedding := (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ (AmbientIsomorphisms.embeddedAmbientIso e T).hom) h.embedding)

/-- Changing ambient coordinates commutes with pulling back an embedded object. -/
def PolarizedIsomorphisms.EmbeddedLevelIso.changeAmbientPullback (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N U)
    (e : P ≅ Q) (f : T ⟶ U) :
    PolarizedIsomorphisms.EmbeddedLevelIso ((A.changeAmbient e).pullback f) ((A.pullback f).changeAmbient e) where
  iso := Moduli.Isomorphisms.LevelPreservingIso.refl (A.object.pullback f.left)
  embedding := by
    change 𝟙 _ ≫ ((A.pullback f).embedding ≫ (AmbientIsomorphisms.embeddedAmbientIso e T).hom) =
      ((A.changeAmbient e).pullback f).embedding
    rw [Category.id_comp]
    apply PullbackComposition.embeddedAmbient_hom_ext f
    let a := (A.pullback f).embedding.left
    let b := ((A.changeAmbient e).pullback f).embedding.left
    let r := CategoryTheory.Limits.pullback.fst A.object.abelian.scheme.hom f.left
    have ha : a ≫ FamilyFunctor.embeddedFamilyAmbientMap P f = r ≫ A.embedding.left :=
      (A.pullback_embedding_isPullback f).w
    have hb : b ≫ FamilyFunctor.embeddedFamilyAmbientMap Q f =
        r ≫ (A.embedding.left ≫ (AmbientIsomorphisms.embeddedAmbientIso e U).hom.left) :=
      ((A.changeAmbient e).pullback_embedding_isPullback f).w
    change (a ≫ (AmbientIsomorphisms.embeddedAmbientIso e T).hom.left) ≫ FamilyFunctor.embeddedFamilyAmbientMap Q f =
      b ≫ FamilyFunctor.embeddedFamilyAmbientMap Q f
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => a ≫ z) (AmbientIsomorphisms.embeddedAmbientIso_naturality e f)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (AmbientIsomorphisms.embeddedAmbientIso e U).hom.left) ha).trans
            ((Category.assoc _ _ _).trans hb.symm))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
