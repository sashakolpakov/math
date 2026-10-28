import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Parameter Poincare Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPoincareCoherence

noncomputable section

/-! The actual Poincare line on a single parameter pullback agrees with
its iterated pullback through the native comparisons of both factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u

private theorem triple_projection
    {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂) (p₃ : X₃ ⟶ Y₃)
    (d₀ : Y₀ ⟶ Y₁) (d₁ : Y₁ ⟶ Y₂) (d₂ : Y₂ ⟶ Y₃)
    (ha : a ≫ p₁ = p₀ ≫ d₀) (hb : b ≫ p₂ = p₁ ≫ d₁)
    (hc : c ≫ p₃ = p₂ ≫ d₂) :
    (a ≫ b ≫ c) ≫ p₃ = p₀ ≫ d₀ ≫ d₁ ≫ d₂ := by
  simp only [Category.assoc, hc, reassoc_of% hb, reassoc_of% ha]

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (D : Dual.Data.DualAbelianData A)
  {U T : Over S} (c : U ⟶ T)

theorem parameterPoincareMap_comp :
    ((D.abelian.parameterPullbackIso c).hom ⊗ₘ (A.parameterPullbackIso c).hom).left ≫
      ((D.pullback T.hom).poincarePullbackOverMap c.left).left ≫
        (D.poincarePullbackOverMap T.hom).left =
      (D.poincarePullbackOverMap U.hom).left := by
  let eD := D.abelian.parameterPullbackIso c
  let eA := A.parameterPullbackIso c
  let e := (eD.hom ⊗ₘ eA.hom).left
  let rC := ((D.pullback T.hom).poincarePullbackOverMap c.left).left
  let rT := (D.poincarePullbackOverMap T.hom).left
  let rU := (D.poincarePullbackOverMap U.hom).left
  have hD : eD.hom.left ≫
      pullback.fst (D.abelian.pullback T.hom).scheme.hom c.left ≫
        pullback.fst D.abelian.scheme.hom T.hom =
      pullback.fst D.abelian.scheme.hom U.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pullback.fst D.abelian.scheme.hom T.hom)
        (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst c D.abelian.scheme)).trans
          (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c D.abelian.scheme))
  have hA : eA.hom.left ≫ pullback.fst (A.pullback T.hom).scheme.hom c.left ≫
      pullback.fst A.scheme.hom T.hom = pullback.fst A.scheme.hom U.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pullback.fst A.scheme.hom T.hom)
        (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst c A.scheme)).trans
          (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A.scheme))
  have hrTf : rT ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      (fst (D.abelian.pullback T.hom).scheme (A.pullback T.hom).scheme).left ≫
        pullback.fst D.abelian.scheme.hom T.hom := D.poincarePullbackOverMap_left_fst T.hom
  have hrTs : rT ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      (snd (D.abelian.pullback T.hom).scheme (A.pullback T.hom).scheme).left ≫
        pullback.fst A.scheme.hom T.hom := D.poincarePullbackOverMap_left_snd T.hom
  have hrCf : rC ≫
      (fst (D.abelian.pullback T.hom).scheme (A.pullback T.hom).scheme).left =
      (fst ((D.abelian.pullback T.hom).pullback c.left).scheme
        ((A.pullback T.hom).pullback c.left).scheme).left ≫
          pullback.fst (D.abelian.pullback T.hom).scheme.hom c.left :=
    (D.pullback T.hom).poincarePullbackOverMap_left_fst c.left
  have hrCs : rC ≫
      (snd (D.abelian.pullback T.hom).scheme (A.pullback T.hom).scheme).left =
      (snd ((D.abelian.pullback T.hom).pullback c.left).scheme
        ((A.pullback T.hom).pullback c.left).scheme).left ≫
          pullback.fst (A.pullback T.hom).scheme.hom c.left :=
    (D.pullback T.hom).poincarePullbackOverMap_left_snd c.left
  have hef : e ≫
      (fst ((D.abelian.pullback T.hom).pullback c.left).scheme
        ((A.pullback T.hom).pullback c.left).scheme).left =
      (fst (D.abelian.pullback U.hom).scheme (A.pullback U.hom).scheme).left ≫ eD.hom.left :=
    Over.tensorHom_left_fst _ _ _ _
  have hes : e ≫
      (snd ((D.abelian.pullback T.hom).pullback c.left).scheme
        ((A.pullback T.hom).pullback c.left).scheme).left =
      (snd (D.abelian.pullback U.hom).scheme (A.pullback U.hom).scheme).left ≫ eA.hom.left :=
    Over.tensorHom_left_snd _ _ _ _
  change e ≫ rC ≫ rT = rU
  apply Over.tensorObj_ext
  · calc
      (e ≫ rC ≫ rT) ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
          (fst (D.abelian.pullback U.hom).scheme (A.pullback U.hom).scheme).left ≫
            eD.hom.left ≫ pullback.fst (D.abelian.pullback T.hom).scheme.hom c.left ≫
              pullback.fst D.abelian.scheme.hom T.hom := by
        exact triple_projection e rC rT _ _ _ _ _ _ _ hef hrCf hrTf
      _ = (fst (D.abelian.pullback U.hom).scheme (A.pullback U.hom).scheme).left ≫
          pullback.fst D.abelian.scheme.hom U.hom := congrArg (fun z => _ ≫ z) hD
      _ = rU ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom :=
        (D.poincarePullbackOverMap_left_fst U.hom).symm
  · calc
      (e ≫ rC ≫ rT) ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
          (snd (D.abelian.pullback U.hom).scheme (A.pullback U.hom).scheme).left ≫
            eA.hom.left ≫ pullback.fst (A.pullback T.hom).scheme.hom c.left ≫
              pullback.fst A.scheme.hom T.hom := by
        exact triple_projection e rC rT _ _ _ _ _ _ _ hes hrCs hrTs
      _ = (snd (D.abelian.pullback U.hom).scheme (A.pullback U.hom).scheme).left ≫
          pullback.fst A.scheme.hom U.hom := congrArg (fun z => _ ≫ z) hA
      _ = rU ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom :=
        (D.poincarePullbackOverMap_left_snd U.hom).symm

def parameterPoincareIso :
    (D.pullback U.hom).poincare.sheaf ≅
      ((((D.pullback T.hom).pullback c.left).poincare).pullback
        ((D.abelian.parameterPullbackIso c).hom ⊗ₘ (A.parameterPullbackIso c).hom).left).sheaf :=
  ((Scheme.Modules.pullback
      ((D.abelian.parameterPullbackIso c).hom ⊗ₘ (A.parameterPullbackIso c).hom).left).mapIso
        ((Scheme.Modules.pullbackComp
          ((D.pullback T.hom).poincarePullbackOverMap c.left).left
          (D.poincarePullbackOverMap T.hom).left).app D.poincare.sheaf) ≪≫
    (Scheme.Modules.pullbackComp
      ((D.abelian.parameterPullbackIso c).hom ⊗ₘ (A.parameterPullbackIso c).hom).left
      (((D.pullback T.hom).poincarePullbackOverMap c.left).left ≫
        (D.poincarePullbackOverMap T.hom).left)).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (parameterPoincareMap_comp A D c)).app D.poincare.sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPoincareCoherence
