import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SmallCharacters

/-! # Representability Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: descent of character-sheaf representability
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u v w z

namespace RepresentabilityDescent.Construction.Representability

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]

/-- A representation pulls back along a left adjoint to the image of
its representing object under the right adjoint. -/
def alongAdjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {F : Dᵒᵖ ⥤ Type z} {Y : D} (r : F.RepresentableBy Y) :
    (L.op ⋙ F).RepresentableBy (R.obj Y) where
  homEquiv := (adj.homEquiv _ _).symm.trans r.homEquiv
  homEquiv_comp f g := by
    exact (congrArg r.homEquiv (adj.homEquiv_naturality_left_symm f g)).trans
      (r.homEquiv_comp (L.map f) _)

/-- An equivalence of test categories reflects representability. -/
theorem of_equivalence (e : C ≌ D) (F : Cᵒᵖ ⥤ Type z)
    [(e.inverse.op ⋙ F).IsRepresentable] : F.IsRepresentable := by
  let r := alongAdjunction e.toAdjunction (e.inverse.op ⋙ F).representableBy
  let i : e.functor.op ⋙ e.inverse.op ⋙ F ≅ F :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op e.unitIso) F ≪≫ F.leftUnitor
  exact (r.ofIso i).isRepresentable

end RepresentabilityDescent.Construction.Representability

/-- A finite locally free representative is in particular a genuine
representation of the underlying presheaf. -/
theorem CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable.isRepresentable {S : Scheme.{u}}
    {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable F) : F.obj.IsRepresentable := by
  obtain ⟨X, _, _, _, ⟨i⟩⟩ := h
  exact ((Functor.RepresentableBy.equivUliftYonedaIso F.obj X).symm
    ((sheafToPresheaf _ _).mapIso i)).isRepresentable

/-- Representability of characters after a base change implies
representability of the corresponding iterated-slice restriction. -/
theorem RepresentabilityDescent.Construction.Schemes.nativeCharacterRestriction_isRepresentable {S : Scheme.{u}}
    (G : Grp (Over S)) (U : Over S)
    (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable
      (CharacterSheaf.Construction.Schemes.characterSheaf U.left ((Over.pullback U.hom).mapGrp.obj G))) :
    ((Over.forget U).op ⋙ SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).IsRepresentable := by
  apply Functor.isRepresentable_comp_uliftFunctor_iff.mp
  let F := (Over.forget U).op ⋙ (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj
  let e := U.iteratedSliceEquiv
  let hchar := h.isRepresentable
  let i : e.inverse.op ⋙ F ≅
      (CharacterSheaf.Construction.Schemes.characterSheaf U.left ((Over.pullback U.hom).mapGrp.obj G)).obj :=
    CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso U.hom G
  let : (e.inverse.op ⋙ F).IsRepresentable :=
    isRepresentable_of_natIso _ i.symm
  let : F.IsRepresentable := RepresentabilityDescent.Construction.Representability.of_equivalence e F
  exact isRepresentable_of_natIso F
    (Functor.isoWhiskerLeft (Over.forget U).op (SmallCharacters.Construction.Schemes.nativeCharacterPresheafIso S G)).symm

/-- The big Zariski topology on a slice is contained in its fppf topology. -/
theorem RepresentabilityDescent.Construction.Schemes.zariskiOver_le_fppfOver (S : Scheme.{u}) :
    Scheme.zariskiTopology.over S ≤ Scheme.fppfTopology.over S := by
  intro X R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hR

/-- The actual native character presheaf is also a Zariski sheaf. -/
def RepresentabilityDescent.Construction.Schemes.nativeCharacterZariskiSheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    Sheaf (Scheme.zariskiTopology.over S) (Type u) :=
  ⟨SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G,
    (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf_isSheaf S G).of_le (RepresentabilityDescent.Construction.Schemes.zariskiOver_le_fppfOver S)⟩

/-- Local finite locally free representatives on an open base cover
give a global representative of the character sheaf. -/
theorem RepresentabilityDescent.Construction.Schemes.nativeCharacter_isRepresentable_of_openCover {S : Scheme.{u}}
    (G : Grp (Over S)) (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable
      (CharacterSheaf.Construction.Schemes.characterSheaf (𝒰.X i) ((Over.pullback (𝒰.f i)).mapGrp.obj G))) :
    (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).IsRepresentable :=
  LocalRepresentatives.Construction.Schemes.isRepresentable_of_openCover (RepresentabilityDescent.Construction.Schemes.nativeCharacterZariskiSheaf S G) 𝒰
    (fun i => RepresentabilityDescent.Construction.Schemes.nativeCharacterRestriction_isRepresentable G (Over.mk (𝒰.f i)) (h i))

/-- A scheme representing a finite locally free representable sheaf
itself has a finite, flat, finitely presented structure morphism. -/
theorem RepresentabilityDescent.Construction.Schemes.finiteLocallyFree_of_pointSheafIso {S : Scheme.{u}} (X : Over S)
    {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (i : CharacterFunctor.Construction.Schemes.pointSheaf S X ≅ F) (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable F) :
    IsFinite X.hom ∧ Flat X.hom ∧ LocallyOfFinitePresentation X.hom := by
  obtain ⟨Y, hf, hflat, hfp, ⟨j⟩⟩ := h
  let : IsFinite Y.hom := hf
  let : Flat Y.hom := hflat
  let : LocallyOfFinitePresentation Y.hom := hfp
  let e : X ≅ Y := uliftYoneda.{u + 1}.preimageIso
    ((sheafToPresheaf _ _).mapIso (i ≪≫ j.symm))
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have hw : e.hom.left ≫ Y.hom = X.hom := e.hom.w
  rw [← hw]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- For a represented sheaf, finite local freeness of the representing
scheme can be checked after restricting to an open cover of the base. -/
theorem RepresentabilityDescent.Construction.Schemes.finiteLocallyFree_of_localRepresentatives {S : Scheme.{u}} (X : Over S)
    {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (i : CharacterFunctor.Construction.Schemes.pointSheaf S X ≅ F) (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ k, CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable
      ((Scheme.fppfTopology.overMapPullback (Type (u + 1)) (𝒰.f k)).obj F)) :
    IsFinite X.hom ∧ Flat X.hom ∧ LocallyOfFinitePresentation X.hom := by
  let : IsZariskiLocalAtTarget (@IsFinite.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  let : IsZariskiLocalAtTarget (@Flat.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ Flat.instHasRingHomPropertyFlat
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _
      instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation
  have hlocal (k : 𝒰.I₀) := RepresentabilityDescent.Construction.Schemes.finiteLocallyFree_of_pointSheafIso
    ((Over.pullback (𝒰.f k)).obj X)
    ((CharacterBaseChange.Construction.Schemes.pointBaseChangeIso (𝒰.f k) X).symm ≪≫
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (𝒰.f k)).mapIso i) (h k)
  exact ⟨IsZariskiLocalAtTarget.of_openCover (P := @IsFinite.{u}) 𝒰
      (fun k => (hlocal k).1),
    IsZariskiLocalAtTarget.of_openCover (P := @Flat.{u}) 𝒰
      (fun k => (hlocal k).2.1),
    IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation.{u}) 𝒰
      (fun k => (hlocal k).2.2)⟩

/-- Finite locally free representability of the actual character sheaf
is local on an open cover of an arbitrary base scheme. -/
theorem RepresentabilityDescent.Construction.Schemes.character_finiteLocallyFree_of_openCover {S : Scheme.{u}}
    (G : Grp (Over S)) (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ k, CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable
      (CharacterSheaf.Construction.Schemes.characterSheaf (𝒰.X k) ((Over.pullback (𝒰.f k)).mapGrp.obj G))) :
    CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable (CharacterSheaf.Construction.Schemes.characterSheaf S G) := by
  let : (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).IsRepresentable :=
    RepresentabilityDescent.Construction.Schemes.nativeCharacter_isRepresentable_of_openCover G 𝒰 h
  let X := (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).reprX
  let r := (Functor.representableByUliftFunctorEquiv.symm
    (SmallCharacters.Construction.Schemes.nativeCharacterPresheaf S G).representableBy).ofIso (SmallCharacters.Construction.Schemes.nativeCharacterPresheafIso S G)
  let i : CharacterFunctor.Construction.Schemes.pointSheaf S X ≅ CharacterSheaf.Construction.Schemes.characterSheaf S G :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      ((Functor.RepresentableBy.equivUliftYonedaIso (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj X) r)
  obtain ⟨hf, hflat, hfp⟩ := RepresentabilityDescent.Construction.Schemes.finiteLocallyFree_of_localRepresentatives X i 𝒰
    (fun k => (h k).of_iso (CharacterBaseChange.Construction.Schemes.characterBaseChangeIso (𝒰.f k) G).symm)
  exact ⟨X, hf, hflat, hfp, ⟨i⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
