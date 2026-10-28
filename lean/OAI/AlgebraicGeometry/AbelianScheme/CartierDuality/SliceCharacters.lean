import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Slice Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceCharacters

noncomputable section

/-!
# CartierDuality: characters on a test scheme

Restricted group-valued functors of points are represented in the slice
category. The group structure is recovered from the represented functor,
so no additional assumption about a character representation is introduced.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj
open scoped _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v

namespace Construction.Slices

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

instance e56StarMonoidal (T : C) : (Over.star T).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- Group-valued points restricted to objects over T. -/
abbrev sliceGroupPoints (T : C) (G : Grp C) : (Over T)ᵒᵖ ⥤ GrpCat.{v} :=
  (Over.forget T).op ⋙ yonedaGrp.obj G

/-- The forgetful/product adjunction represents the restricted point functor. -/
def sliceGroupRepresentation (T : C) (G : Grp C) :
    (sliceGroupPoints T G ⋙ forget GrpCat).RepresentableBy ((Over.star T).obj G.X) :=
  Functor.representableByEquiv.symm ((Over.forgetAdjStar T).compYonedaIso.app G.X)

/-- The base change of G as the group object representing its restricted
functor of points. Its underlying object is T × G → T. -/
def sliceGroup (T : C) (G : Grp C) : Grp (Over T) := by
  let X := (Over.star T).obj G.X
  letI : GrpObj X := GrpObj.ofRepresentableBy X (sliceGroupPoints T G)
    (sliceGroupRepresentation T G)
  exact Grp.mk X

/-- The representing isomorphism respects the group structure. -/
def sliceGroupPointIso (T : C) (G : Grp C) :
    sliceGroupPoints T G ≅ yonedaGrp.obj (sliceGroup T G) :=
  (yonedaGrpObjIsoOfRepresentableBy ((Over.star T).obj G.X)
    (sliceGroupPoints T G) (sliceGroupRepresentation T G)).symm

/-- The product adjunction on points preserves the group law supplied by
the ordinary pullback group construction. -/
def starPointMulEquiv (T : C) (G : Grp C) (U : Over T) :
    ((Over.forget T).obj U ⟶ G.X) ≃* (U ⟶ (Over.star T).obj G.X) where
  toEquiv := (Over.forgetAdjStar T).homEquiv U G.X
  map_mul' f g := by
    change (Over.forgetAdjStar T).unit.app U ≫ (Over.star T).map (f * g) =
      ((Over.forgetAdjStar T).unit.app U ≫ (Over.star T).map f) *
        ((Over.forgetAdjStar T).unit.app U ≫ (Over.star T).map g)
    rw [Functor.map_mul, MonObj.comp_mul]

/-- Restricted group-valued points are represented by the native image
under the product functor, with its native group structure. -/
def starGroupPointIso (T : C) (G : Grp C) :
    sliceGroupPoints T G ≅ yonedaGrp.obj ((Over.star T).mapGrp.obj G) :=
  NatIso.ofComponents (fun U => (starPointMulEquiv T G U.unop).toGrpIso) (by
    intro U V f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact (Over.forgetAdjStar T).homEquiv_naturality_left f.unop g)

omit [HasPullbacks C] in
/-- A restricted natural group homomorphism is evaluated by pulling back
its value at the universal point of T × G. -/
theorem sliceNatTrans_apply (T : C) (G K : Grp C)
    (χ : sliceGroupPoints T G ⟶ sliceGroupPoints T K)
    (U : Over T) (f : U.left ⟶ G.X) :
    χ.app (Opposite.op U) f =
      ((Over.forgetAdjStar T).homEquiv U G.X f).left ≫
        χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd := by
  let k := (Over.forgetAdjStar T).homEquiv U G.X f
  have hk : k.left ≫ Limits.prod.snd = f := by
    have h := ((Over.forgetAdjStar T).homEquiv U G.X).symm_apply_apply f
    simp only [Adjunction.homEquiv_counit, Over.forget_map,
      Over.forgetAdjStar_counit_app] at h
    exact h
  have h := congrArg
    (fun p : (sliceGroupPoints T G).obj (Opposite.op ((Over.star T).obj G.X)) ⟶
        (sliceGroupPoints T K).obj (Opposite.op U) => p.hom Limits.prod.snd)
    (χ.naturality k.op)
  change χ.app (Opposite.op U) (k.left ≫ Limits.prod.snd) =
    k.left ≫ χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd at h
  exact (congrArg (fun g : U.left ⟶ G.X => χ.app (Opposite.op U) g) hk.symm).trans h

omit [HasPullbacks C] in
/-- Equality of characters can be checked at the universal test point. -/
theorem sliceNatTrans_ext (T : C) (G K : Grp C)
    {χ ψ : sliceGroupPoints T G ⟶ sliceGroupPoints T K}
    (h : χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd =
      ψ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd) : χ = ψ := by
  ext U f
  rw [sliceNatTrans_apply T G K χ U.unop f, sliceNatTrans_apply T G K ψ U.unop f, h]

/-- Characters expressed directly through the native product functor. -/
def starCharacterEquiv (T : C) (G K : Grp C) :
    (sliceGroupPoints T G ⟶ sliceGroupPoints T K) ≃
      ((Over.star T).mapGrp.obj G ⟶ (Over.star T).mapGrp.obj K) :=
  (starGroupPointIso T G).homFromEquiv.trans <|
    (starGroupPointIso T K).homToEquiv.trans <|
      (yonedaGrpFullyFaithful (C := Over T)).homEquiv.symm

/-- The group morphism corresponding to a character is obtained from its
value on the universal point by the product adjunction. -/
theorem starCharacterEquiv_underlying (T : C) (G K : Grp C)
    (χ : sliceGroupPoints T G ⟶ sliceGroupPoints T K) :
    (starCharacterEquiv T G K χ).hom.hom =
      (Over.forgetAdjStar T).homEquiv ((Over.star T).obj G.X) K.X
        (χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd) := by
  change (Over.forgetAdjStar T).homEquiv ((Over.star T).obj G.X) K.X
    (χ.app (Opposite.op ((Over.star T).obj G.X))
      (((Over.forgetAdjStar T).homEquiv ((Over.star T).obj G.X) G.X).symm (𝟙 _))) = _
  rw [Adjunction.homEquiv_symm_id, Over.forgetAdjStar_counit_app]

omit [HasPullbacks C] in
/-- Explicit underlying map in the product adjunction. -/
theorem starAdjunction_homEquiv_left (T Y : C) (U : Over T) (f : U.left ⟶ Y) :
    ((Over.forgetAdjStar T).homEquiv U Y f).left = Limits.prod.lift U.hom f := by
  change ((Over.forgetAdjStar T).unit.app U).left ≫ ((Over.star T).map f).left = _
  simp only [Over.forgetAdjStar_unit_app_left, Over.star_map_left]
  exact (Limits.prod.lift_map U.hom (𝟙 U.left) (𝟙 T) f).trans
    (by rw [Category.comp_id, Category.id_comp])

/-- Projecting the represented group morphism to its second factor
recovers the original universal-point value of the character. -/
theorem starCharacterEquiv_snd (T : C) (G K : Grp C)
    (χ : sliceGroupPoints T G ⟶ sliceGroupPoints T K) :
    (starCharacterEquiv T G K χ).hom.hom.left ≫ Limits.prod.snd =
      χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd := by
  have h1 := congrArg (fun f : (Over.star T).obj G.X ⟶ (Over.star T).obj K.X =>
    f.left ≫ Limits.prod.snd) (starCharacterEquiv_underlying T G K χ)
  have h2 := congrArg (fun f : T ⨯ G.X ⟶ T ⨯ K.X => f ≫ Limits.prod.snd)
    (starAdjunction_homEquiv_left T K.X ((Over.star T).obj G.X)
      (χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd))
  exact h1.trans (h2.trans (Limits.prod.lift_snd _ _))

omit [HasPullbacks C] in
/-- Restricting a character along a test-scheme morphism pulls back its
universal-point value along the product of that morphism with G. -/
theorem sliceNatTrans_restrict_universal {T U : C} (p : U ⟶ T) (G K : Grp C)
    (χ : sliceGroupPoints T G ⟶ sliceGroupPoints T K) :
    (Functor.whiskerLeft (Over.map p).op χ).app
      (Opposite.op ((Over.star U).obj G.X)) Limits.prod.snd =
    Limits.prod.map p (𝟙 G.X) ≫
      χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd := by
  change χ.app (Opposite.op ((Over.map p).obj ((Over.star U).obj G.X)))
    Limits.prod.snd = _
  have h := sliceNatTrans_apply T G K χ ((Over.map p).obj ((Over.star U).obj G.X))
    Limits.prod.snd
  have hk : ((Over.forgetAdjStar T).homEquiv
      ((Over.map p).obj ((Over.star U).obj G.X)) G.X Limits.prod.snd).left =
        Limits.prod.map p (𝟙 G.X) := by
    calc
      _ = Limits.prod.lift (Limits.prod.fst ≫ p) Limits.prod.snd := by
        have he : ((Over.star U).obj G.X).hom = (Limits.prod.fst : U ⨯ G.X ⟶ U) := by
          simp only [Over.star_obj_hom]
          exact Limits.prod.lift_fst _ _
        have hp : ((Over.map p).obj ((Over.star U).obj G.X)).hom =
            Limits.prod.fst ≫ p := congrArg (fun q => q ≫ p) he
        exact (starAdjunction_homEquiv_left T G.X
          ((Over.map p).obj ((Over.star U).obj G.X)) Limits.prod.snd).trans
          (congrArg (fun q : U ⨯ G.X ⟶ T => Limits.prod.lift q Limits.prod.snd) hp)
      _ = _ := by
        apply Limits.prod.hom_ext
        · simp only [Limits.prod.lift_fst, Limits.prod.map_fst]
        · simp only [Limits.prod.lift_snd, Limits.prod.map_snd, Category.comp_id]
  exact h.trans (congrArg
    (fun q : U ⨯ G.X ⟶ T ⨯ G.X =>
      q ≫ χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd) hk)

/-- The group recovered from representability agrees with the native
group object obtained by the product functor. -/
def sliceGroupNativeIso (T : C) (G : Grp C) :
    sliceGroup T G ≅ (Over.star T).mapGrp.obj G :=
  (yonedaGrpFullyFaithful (C := Over T)).preimageIso
    ((sliceGroupPointIso T G).symm ≪≫ starGroupPointIso T G)

/-- Internal-Hom sections over T are actual morphisms of the base-changed
group objects over T. -/
def sliceCharacterEquiv (T : C) (G K : Grp C) :
    (sliceGroupPoints T G ⟶ sliceGroupPoints T K) ≃
      (sliceGroup T G ⟶ sliceGroup T K) :=
  (sliceGroupPointIso T G).homFromEquiv.trans <|
    (sliceGroupPointIso T K).homToEquiv.trans <|
      (yonedaGrpFullyFaithful (C := Over T)).homEquiv.symm

end Construction.Slices

namespace Construction.Schemes

open _root_.AlgebraicGeometry

instance e56IteratedSliceForwardMonoidal
    (S : Scheme.{u}) (T : Over S) : T.iteratedSliceForward.Monoidal := by
  have : T.iteratedSliceForward.IsEquivalence :=
    inferInstanceAs (T.iteratedSliceEquiv.functor.IsEquivalence)
  exact Functor.Monoidal.ofChosenFiniteProducts _

/-- The product right adjoint in the slice, followed by the double-slice
equivalence, is the ordinary scheme pullback functor. -/
def sliceProductPullbackIso (S : Scheme.{u}) (T : Over S) :
    Over.star T ⋙ T.iteratedSliceForward ≅ Over.pullback T.hom :=
  (T.iteratedSliceEquiv.symm.toAdjunction.comp (Over.forgetAdjStar T)).rightAdjointUniq
    (Over.mapPullbackAdj T.hom)

/-- The comparison between product in the slice and native pullback
preserves the projection to the original scheme. -/
theorem sliceProductPullbackIso_fst (S : Scheme.{u}) (T Y : Over S) :
    ((sliceProductPullbackIso S T).hom.app Y).left ≫ Limits.pullback.fst Y.hom T.hom =
      (Limits.prod.snd : T ⨯ Y ⟶ Y).left := by
  have h := (T.iteratedSliceEquiv.symm.toAdjunction.comp (Over.forgetAdjStar T)).rightAdjointUniq_hom_app_counit
    (Over.mapPullbackAdj T.hom) Y
  have h' := congrArg
    (fun f : (Over.map T.hom).obj ((Over.star T ⋙ T.iteratedSliceForward).obj Y) ⟶ Y => f.left) h
  simp only [Adjunction.comp_counit_app, Over.mapPullbackAdj_counit_app,
    Over.forgetAdjStar_counit_app] at h'
  change ((sliceProductPullbackIso S T).hom.app Y).left ≫ Limits.pullback.fst Y.hom T.hom =
    𝟙 _ ≫ (Limits.prod.snd : T ⨯ Y ⟶ Y).left at h'
  exact h'.trans (Category.id_comp _)

/-- The group over a test scheme recovered from its restricted functor of
points, expressed in the ordinary category of schemes over that test scheme. -/
def testSchemeGroup (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    Grp (Over T.left) :=
  T.iteratedSliceForward.mapGrp.obj (Slices.sliceGroup T G)

/-- Its underlying scheme is canonically the scheme-theoretic pullback. -/
def testSchemeGroup_underlyingIso
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (testSchemeGroup S G T).X ≅ (Over.pullback T.hom).obj G.X :=
  (sliceProductPullbackIso S T).app G.X

/-- The comparison is an isomorphism of group schemes, including their
group laws, rather than only an isomorphism of underlying schemes. -/
def starSchemeGroup_pullbackIso
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    T.iteratedSliceForward.mapGrp.obj ((Over.star T).mapGrp.obj G) ≅
      (Over.pullback T.hom).mapGrp.obj G :=
  (Functor.mapGrpCompIso (F := Over.star T) (G := T.iteratedSliceForward)).symm.app G ≪≫
    (Functor.mapGrpNatIso (sliceProductPullbackIso S T)).app G

/-- The group-scheme comparison uses the same underlying scheme map as
the product/pullback adjunction comparison. -/
theorem starSchemeGroup_pullbackIso_hom_left
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (starSchemeGroup_pullbackIso S G T).hom.hom.hom.left =
      ((sliceProductPullbackIso S T).hom.app G.X).left := by
  change (𝟙 _ ≫ (sliceProductPullbackIso S T).hom.app G.X).left = _
  change 𝟙 _ ≫ ((sliceProductPullbackIso S T).hom.app G.X).left = _
  exact Category.id_comp _

/-- The representability construction agrees with native pullback as a
group scheme. -/
def testSchemeGroup_pullbackIso
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    testSchemeGroup S G T ≅ (Over.pullback T.hom).mapGrp.obj G :=
  T.iteratedSliceForward.mapGrp.mapIso (Slices.sliceGroupNativeIso T G) ≪≫
    starSchemeGroup_pullbackIso S G T

/-- Pulling back the integral multiplicative-group model is independent
of the intermediate base scheme. -/
theorem pullback_eqIso_inv_fst {S T : Scheme.{u}} (f g : T ⟶ S) (h : f = g)
    (G : Grp (Over S)) :
    ((Functor.mapGrpNatIso (eqToIso (congrArg (fun k : T ⟶ S => Over.pullback k) h))).inv.app G).hom.hom.left ≫
      Limits.pullback.fst G.X.hom f = Limits.pullback.fst G.X.hom g := by
  cases h
  change 𝟙 _ ≫ Limits.pullback.fst G.X.hom f = _
  exact Category.id_comp _

/-- The canonical comparison of successive pullbacks preserves the
composite projection to the original scheme. -/
theorem pullbackComp_hom_fst {B S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ B) (Y : Over B) :
    ((Over.pullbackComp f g).hom.app Y).left ≫
      Limits.pullback.fst (Limits.pullback.snd Y.hom g) f ≫ Limits.pullback.fst Y.hom g =
        Limits.pullback.fst Y.hom (f ≫ g) := by
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv Y
  have h' := congrArg
    (fun h : (Over.map f ⋙ Over.map g).obj ((Over.pullback (f ≫ g)).obj Y) ⟶ Y => h.left) h
  simp only [Adjunction.comp_counit_app, Over.mapPullbackAdj_counit_app] at h'
  change ((Over.pullbackComp f g).hom.app Y).left ≫
      Limits.pullback.fst (Limits.pullback.snd Y.hom g) f ≫ Limits.pullback.fst Y.hom g =
        𝟙 _ ≫ Limits.pullback.fst Y.hom (f ≫ g) at h'
  exact h'.trans (Category.id_comp _)

/-- Pulling back the integral multiplicative-group model is independent
of the intermediate base scheme. -/
def multiplicativeGroup_pullbackFunctorIso
    {S T : Scheme.{u}} (f : T ⟶ S) :
    Over.pullback (specULiftZIsTerminal.from S) ⋙ Over.pullback f ≅
      Over.pullback (specULiftZIsTerminal.from T) :=
  (Over.pullbackComp f (specULiftZIsTerminal.from S)).symm ≪≫
    eqToIso (congrArg (fun g : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) => Over.pullback g)
      (specULiftZIsTerminal.hom_ext _ _))

/-- The multiplicative group commutes with arbitrary scheme base change. -/
def multiplicativeGroup_pullbackIso {S T : Scheme.{u}} (f : T ⟶ S) :
    (Over.pullback f).mapGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ≅
      CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T :=
  (Functor.mapGrpCompIso (F := Over.pullback (specULiftZIsTerminal.from S))
    (G := Over.pullback f)).symm.app (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)) ≪≫
      (Functor.mapGrpNatIso (multiplicativeGroup_pullbackFunctorIso f)).app
        (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ))

/-- Projection of the relative multiplicative group to its integral model. -/
def multiplicativeGroupToIntegral (S : Scheme.{u}) :
    (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X.left ⟶ (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.left :=
  Limits.pullback.fst (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.hom
    (specULiftZIsTerminal.from S)

/-- The multiplicative-group base-change isomorphism preserves the
projection to the integral model, for arbitrary base schemes. -/
theorem multiplicativeGroup_pullbackIso_inv_integralProjection
    {S T : Scheme.{u}} (f : T ⟶ S) :
    (multiplicativeGroup_pullbackIso f).inv.hom.hom.left ≫
      Limits.pullback.fst (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X.hom f ≫
        multiplicativeGroupToIntegral S = multiplicativeGroupToIntegral T := by
  let G₀ := Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)
  let g := specULiftZIsTerminal.from S
  have h : f ≫ g = specULiftZIsTerminal.from T := specULiftZIsTerminal.hom_ext _ _
  let i : Over.pullback (f ≫ g) ≅ Over.pullback (specULiftZIsTerminal.from T) :=
    eqToIso (congrArg (fun k : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) => Over.pullback k) h)
  change ((Functor.mapGrpNatIso i).inv.app G₀).hom.hom.left ≫
    ((Over.pullbackComp f g).hom.app G₀.X).left ≫
      Limits.pullback.fst (Limits.pullback.snd G₀.X.hom g) f ≫
        Limits.pullback.fst G₀.X.hom g = _
  exact (congrArg (fun k => ((Functor.mapGrpNatIso i).inv.app G₀).hom.hom.left ≫ k)
    (pullbackComp_hom_fst f g G₀.X)).trans
    (pullback_eqIso_inv_fst (f ≫ g) (specULiftZIsTerminal.from T) h G₀)

/-- On a test scheme, the character sheaf classifies group morphisms in
the corresponding slice. The iterated slice is canonically equivalent
to the category of schemes over the underlying test scheme. -/
def characterSheaf_sectionsEquiv
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ≃
      (Slices.sliceGroup T G ⟶ Slices.sliceGroup T (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) :=
  Slices.sliceCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)

/-- Characters over a test scheme are actual group-scheme morphisms over
that scheme; the represented source and target have the pullback schemes
identified by `testSchemeGroup_underlyingIso`. -/
def characterSheaf_sectionsOverEquiv
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ≃
      (testSchemeGroup S G T ⟶ testSchemeGroup S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) T) := by
  let h : T.iteratedSliceForward.FullyFaithful := T.iteratedSliceEquiv.fullyFaithfulFunctor
  exact (characterSheaf_sectionsEquiv S G T).trans h.mapGrp.homEquiv

/-- The character sheaf on a test scheme classifies homomorphisms between
the native scheme-theoretic pullback group schemes. -/
def characterSheaf_sectionsPullbackEquiv
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ≃
      ((Over.pullback T.hom).mapGrp.obj G ⟶
        (Over.pullback T.hom).mapGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) := by
  let h : T.iteratedSliceForward.FullyFaithful := T.iteratedSliceEquiv.fullyFaithfulFunctor
  exact (Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)).trans <|
    h.mapGrp.homEquiv.trans <|
      (starSchemeGroup_pullbackIso S G T).homFromEquiv.trans <|
        (starSchemeGroup_pullbackIso S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) T).homToEquiv

/-- Explicit formula for converting a character section into a native
pullback group-scheme homomorphism. -/
theorem characterSheaf_sectionsPullbackEquiv_eq
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    characterSheaf_sectionsPullbackEquiv S G T χ =
      (starSchemeGroup_pullbackIso S G T).inv ≫
        T.iteratedSliceForward.mapGrp.map
          (Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ) ≫
            (starSchemeGroup_pullbackIso S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) T).hom := by
  exact Category.assoc (starSchemeGroup_pullbackIso S G T).inv
    (T.iteratedSliceForward.mapGrp.map
      (Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ))
    (starSchemeGroup_pullbackIso S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) T).hom

/-- On every test scheme, the character sheaf is precisely the group of
group-scheme homomorphisms from the base-changed group into Gₘ. -/
def characterSheaf_testCharacterEquiv
    (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ≃
      ((Over.pullback T.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left) :=
  (characterSheaf_sectionsPullbackEquiv S G T).trans
    (multiplicativeGroup_pullbackIso T.hom).homToEquiv

/-- A character as the corresponding morphism T × G → Gₘ over the
original base. It is determined by evaluation at the universal point. -/
def characterValue (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    T ⨯ G.X ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X :=
  χ.app (Opposite.op ((Over.star T).obj G.X)) Limits.prod.snd

/-- The universal-point evaluation is the underlying native character
morphism followed by projection from the pulled-back multiplicative group. -/
theorem characterValue_native (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    ((sliceProductPullbackIso S T).hom.app G.X).left ≫
      (characterSheaf_sectionsPullbackEquiv S G T χ).hom.hom.left ≫
        Limits.pullback.fst (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X.hom T.hom =
      (characterValue S G T χ).left := by
  let K := CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S
  let k := Slices.starCharacterEquiv T G K χ
  let iG := starSchemeGroup_pullbackIso S G T
  let iK := starSchemeGroup_pullbackIso S K T
  have he : iG.hom ≫ characterSheaf_sectionsPullbackEquiv S G T χ =
      T.iteratedSliceForward.mapGrp.map k ≫ iK.hom := by
    exact (congrArg (fun f => iG.hom ≫ f)
      (characterSheaf_sectionsPullbackEquiv_eq S G T χ)).trans (iG.hom_inv_id_assoc _)
  have hp := congrArg
    (fun f : T.iteratedSliceForward.mapGrp.obj ((Over.star T).mapGrp.obj G) ⟶
        (Over.pullback T.hom).mapGrp.obj K =>
      f.hom.hom.left ≫ Limits.pullback.fst K.X.hom T.hom) he
  change iG.hom.hom.hom.left ≫
      (characterSheaf_sectionsPullbackEquiv S G T χ).hom.hom.left ≫
        Limits.pullback.fst K.X.hom T.hom =
    k.hom.hom.left.left ≫ iK.hom.hom.hom.left ≫ Limits.pullback.fst K.X.hom T.hom at hp
  have hK : iK.hom.hom.hom.left ≫ Limits.pullback.fst K.X.hom T.hom =
      (Limits.prod.snd : T ⨯ K.X ⟶ K.X).left :=
    (congrArg (fun f => f ≫ Limits.pullback.fst K.X.hom T.hom)
      (starSchemeGroup_pullbackIso_hom_left S K T)).trans (sliceProductPullbackIso_fst S T K.X)
  have hEval : k.hom.hom.left.left ≫ (Limits.prod.snd : T ⨯ K.X ⟶ K.X).left =
      (characterValue S G T χ).left :=
    congrArg (fun f : T ⨯ G.X ⟶ K.X => f.left) (Slices.starCharacterEquiv_snd T G K χ)
  have hresult := hp.trans
    ((congrArg (fun f => k.hom.hom.left.left ≫ f) hK).trans hEval)
  exact (congrArg
    (fun f => f ≫ (characterSheaf_sectionsPullbackEquiv S G T χ).hom.hom.left ≫
      Limits.pullback.fst K.X.hom T.hom)
    (starSchemeGroup_pullbackIso_hom_left S G T).symm).trans hresult

/-- The integral value of a character is its native test-scheme
character followed by the integral projection of the multiplicative group. -/
theorem characterValue_integral (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    (characterValue S G T χ).left ≫ multiplicativeGroupToIntegral S =
      ((sliceProductPullbackIso S T).hom.app G.X).left ≫
        (characterSheaf_testCharacterEquiv S G T χ).hom.hom.left ≫
          multiplicativeGroupToIntegral T.left := by
  let K := CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S
  let b := multiplicativeGroup_pullbackIso T.hom
  let e : ((Over.pullback T.hom).mapGrp.obj K).X.left ≅
      (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X.left :=
    (Over.forget T.left).mapIso ((Grp.forget _).mapIso b)
  let p := ((sliceProductPullbackIso S T).hom.app G.X).left
  let k := characterSheaf_sectionsPullbackEquiv S G T χ
  have hb : e.inv ≫ Limits.pullback.fst K.X.hom T.hom ≫ multiplicativeGroupToIntegral S =
      multiplicativeGroupToIntegral T.left :=
    multiplicativeGroup_pullbackIso_inv_integralProjection T.hom
  have hp := (e.hom_inv_id_assoc
    (Limits.pullback.fst K.X.hom T.hom ≫ multiplicativeGroupToIntegral S)).symm.trans
      (congrArg (fun f => e.hom ≫ f) hb)
  have hcomp {V₁ V₂ V₃ V₄ V₅ V₆ : Scheme.{u}}
      (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) (c : V₃ ⟶ V₄) (d : V₁ ⟶ V₄)
      (r : V₄ ⟶ V₆) (e : V₃ ⟶ V₅) (s : V₅ ⟶ V₆)
      (h : a ≫ b ≫ c = d) (hc : c ≫ r = e ≫ s) :
      d ≫ r = a ≫ (b ≫ e) ≫ s := by
    rw [← h]
    simp only [Category.assoc, hc]
  change (characterValue S G T χ).left ≫ multiplicativeGroupToIntegral S =
    p ≫ (k.hom.hom.left ≫ e.hom) ≫ multiplicativeGroupToIntegral T.left
  exact hcomp p k.hom.hom.left _ _ _ e.hom _
    (characterValue_native S G T χ) hp

/-- The universal-point value makes restriction of sheaf sections
explicit, without a choice of coordinates or affineness assumptions. -/
theorem characterValue_restrict (S : Scheme.{u}) (G : Grp (Over S))
    {T U : Over S} (p : U ⟶ T)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    characterValue S G U ((CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map p.op χ) =
      Limits.prod.map p (𝟙 G.X) ≫ characterValue S G T χ :=
  Slices.sliceNatTrans_restrict_universal p G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceCharacters
