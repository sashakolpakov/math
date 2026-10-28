import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismFamiliesId
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor
import Mathlib.CategoryTheory.HomCongr

/-! # Endomorphism Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismHom.EndomorphismFamilies

noncomputable section

/-! The actual endomorphism-family functor embeds in Presentations's relative Hom
functor. The map uses the canonical product/pullback identification and
the map/pullback adjunction, with restriction proved on scheme maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def homSourceSchemeIso (T : Over S) :
    (T ⨯ A.scheme).left ≅ pullback A.scheme.hom T.hom :=
  Over.prodLeftIsoPullback T A.scheme ≪≫ pullbackSymmetry T.hom A.scheme.hom

@[reassoc (attr := simp)] theorem homSourceSchemeIso_fst (T : Over S) :
    (homSourceSchemeIso A T).hom ≫ pullback.fst A.scheme.hom T.hom =
      (prod.snd : T ⨯ A.scheme ⟶ A.scheme).left := by
  simp only [homSourceSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, Over.prodLeftIsoPullback_hom_snd]

@[reassoc (attr := simp)] theorem homSourceSchemeIso_snd (T : Over S) :
    (homSourceSchemeIso A T).hom ≫ pullback.snd A.scheme.hom T.hom =
      (prod.fst : T ⨯ A.scheme ⟶ T).left := by
  simp only [homSourceSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, Over.prodLeftIsoPullback_hom_fst]

def homSourceIso (T : Over S) : T ⨯ A.scheme ≅
    (Over.map T.hom).obj (A.pullback T.hom).scheme :=
  Over.isoMk (homSourceSchemeIso A T) (by
    change (homSourceSchemeIso A T).hom ≫ (pullback.snd A.scheme.hom T.hom ≫ T.hom) = _
    rw [← Category.assoc, homSourceSchemeIso_snd]
    exact (prod.fst : T ⨯ A.scheme ⟶ T).w)

/-- Relative self-maps are exactly the actual maps T × A → A. -/
def relativeHomEquiv (T : Over S) :
    ((A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme) ≃
      (T ⨯ A.scheme ⟶ A.scheme) :=
  ((Over.mapPullbackAdj T.hom).homEquiv (A.pullback T.hom).scheme A.scheme).symm.trans
    ((homSourceIso A T).symm.homCongr (Iso.refl A.scheme))

theorem relativeHomEquiv_left (T : Over S)
    (r : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme) :
    (relativeHomEquiv A T r).left =
      (homSourceSchemeIso A T).hom ≫ r.left ≫ pullback.fst A.scheme.hom T.hom := by
  change (homSourceSchemeIso A T).hom ≫
    (r.left ≫ pullback.fst A.scheme.hom T.hom) ≫ 𝟙 A.scheme.left = _
  rw [Category.comp_id]

theorem homSource_naturality {T U : Over S} (f : T ⟶ U) :
    (homSourceSchemeIso A T).hom ≫ EndomorphismFamiliesId.EndomorphismFamilies.familyMap A f =
      (prod.map f (𝟙 A.scheme)).left ≫ (homSourceSchemeIso A U).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_fst, homSourceSchemeIso_fst, Category.assoc,
      homSourceSchemeIso_fst, ← Over.comp_left, prod.map_snd, Category.comp_id]
  · rw [Category.assoc, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_snd, ← Category.assoc, homSourceSchemeIso_snd,
      Category.assoc, homSourceSchemeIso_snd, ← Over.comp_left]
    exact (congrArg Over.Hom.left (prod.map_fst f (𝟙 A.scheme))).symm

/-- Geometric restriction is the same map as precomposition in Presentations's
relative Hom functor. -/
theorem relativeHom_restrict {T U : Over S} (f : T ⟶ U)
    (r : Finite.Actions.GroupEndRing (A.pullback U.hom)) :
    relativeHomEquiv A T ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A f r).hom (A.pullback T.hom)) =
      prod.map f (𝟙 A.scheme) ≫ relativeHomEquiv A U (r.hom (A.pullback U.hom)) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, relativeHomEquiv_left, relativeHomEquiv_left]
  change (homSourceSchemeIso A T).hom ≫
      EndomorphismFamiliesId.EndomorphismFamilies.endHom A (EndomorphismFamiliesId.EndomorphismFamilies.restrict A f r) ≫ pullback.fst A.scheme.hom T.hom =
    (prod.map f (𝟙 A.scheme)).left ≫
      (homSourceSchemeIso A U).hom ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A r ≫ pullback.fst A.scheme.hom U.hom
  rw [EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst, ← Category.assoc (homSourceSchemeIso A T).hom,
    homSource_naturality, Category.assoc]

/-- Forget only the group-homomorphism equations, retaining the actual
relative scheme morphism. -/
def homInclusion : (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat) ⟶
    HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor A.scheme A.scheme where
  app T := TypeCat.ofHom (fun r => relativeHomEquiv A T.unop (r.hom (A.pullback T.unop.hom)))
  naturality {T U} f := by
    apply ConcreteCategory.ext_apply
    intro r
    exact relativeHom_restrict A f.unop r

theorem homInclusion_injective (T : Over S) :
    Function.Injective ((homInclusion A).app (op T)) := by
  intro r q h
  apply Finite.Actions.GroupEndRing.ext
  exact (relativeHomEquiv A T).injective h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismHom.EndomorphismFamilies
