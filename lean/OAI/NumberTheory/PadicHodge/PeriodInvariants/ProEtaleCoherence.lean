import OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

/-! # Pro Etale Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence

noncomputable section

/-!
# Identity and composition for transport of the actual pro-étale site

The natural isomorphisms preserve the underlying schemes. Their induced
isomorphisms of sheaf functors provide the coherence used in cohomological
Galois actions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

variable {X Y Z : Scheme.{u}}

def proEtaleCongr_refl (X : Scheme.{u}) :
    (IntegralComparison.ProEtale.proEtaleCongr (Iso.refl X)).functor ≅ 𝟭 X.ProEt :=
  MorphismProperty.Comma.mapRightId (P := @WeaklyEtale) (Q := ⊤) (W := ⊤) _ _

def proEtaleCongr_comp (e : X ≅ Y) (f : Y ≅ Z) :
    (IntegralComparison.ProEtale.proEtaleCongr (e ≪≫ f)).functor ≅ (IntegralComparison.ProEtale.proEtaleCongr e).functor ⋙ (IntegralComparison.ProEtale.proEtaleCongr f).functor :=
  NatIso.ofComponents (fun U =>
    MorphismProperty.Comma.isoMk (Iso.refl _) (Iso.refl _) (by
      change (𝟙 U.left) ≫ ((U.hom ≫ e.hom) ≫ f.hom) =
        (U.hom ≫ (e.hom ≫ f.hom)) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id, Category.assoc]))
    (by
      intro U V g
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 V.left = 𝟙 U.left ≫ g.left
      simp only [Category.comp_id, Category.id_comp])

variable (A : Type*) [Category A]

def proEtaleSheafCongr_refl (X : Scheme.{u}) :
    (IntegralComparison.ProEtale.proEtaleSheafCongr A (Iso.refl X)).functor ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (proEtaleCongr_refl X) A (Scheme.ProEt.topology X)

def proEtaleSheafCongr_comp (e : X ≅ Y) (f : Y ≅ Z) :
    (IntegralComparison.ProEtale.proEtaleSheafCongr A e).functor ⋙ (IntegralComparison.ProEtale.proEtaleSheafCongr A f).functor ≅
      (IntegralComparison.ProEtale.proEtaleSheafCongr A (e ≪≫ f)).functor :=
  Functor.sheafPushforwardContinuousComp' (proEtaleCongr_comp f.symm e.symm).symm A
    (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence
