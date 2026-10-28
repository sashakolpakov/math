import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap

/-! # Incoming Reindex Steps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindexSteps

noncomputable section

/-! Simultaneous transport of an actual incoming comparison along
equal ambient opens and a reindexed family of principal opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem compose_three {C : Type*} [Category C] {A B D E : C}
    {a a' : A ⟶ B} {s : B ⟶ E} {t : A ⟶ D} {b b' : D ⟶ E}
    (ha : a = a') (hb : a' ≫ s = t ≫ b) (hc : b = b') : a ≫ s = t ≫ b' :=
  (congrArg (fun z => z ≫ s) ha).trans
    (hb.trans (congrArg (fun z => t ≫ z) hc))

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (V V' : Y.Opens) (hV : V = V')
  {D : Type v} [Preorder D] {E : Type w} [Preorder E]
  (F : D →o Y.Opens) (G : E →o Y.Opens) (r : E ⥤ D)
  (hF : ∀ d, F d ≤ V') (hG : ∀ e, G e ≤ V)
  (h : G = IncomingMap.reindexedOpens F r)
  (K L : CochainComplex
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ)
  (b : ((Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj L)

abbrev restriction :
    (Dᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ⥤
      (Eᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  (Functor.whiskeringLeft _ _ _).obj r.op

local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap.familyIso (p := p) (J := J) (δ := δ)
  f n G (IncomingMap.reindexedOpens F r) h

theorem open_step :
    IncomingMap.map f n V G hG K L
      (IncomingMap.transport f n V K L V' hV b) =
    IncomingMap.map f n V' G (fun d => (hG d).trans hV.le) K L b :=
  IncomingMap.open_eq f n V G hG K L V' hV
    (fun d => (hG d).trans hV.le) b

theorem family_step :
    IncomingMap.map f n V' G (fun d => (hG d).trans hV.le) K L b ≫
      ((NatIso.mapHomologicalComplex s (.up ℕ)).app L).hom =
    ((NatIso.mapHomologicalComplex s (.up ℕ)).app K).hom ≫
      IncomingMap.map f n V'
        (IncomingMap.reindexedOpens F r) (fun d => hF (r.obj d)) K L b :=
  IncomingMap.family_eq f n V' G (fun d => (hG d).trans hV.le)
    K L b (IncomingMap.reindexedOpens F r) h (fun d => hF (r.obj d))

theorem reindex_step :
    IncomingMap.map f n V'
      (IncomingMap.reindexedOpens F r) (fun d => hF (r.obj d)) K L b =
    ((restriction (B := B) r).mapHomologicalComplex (.up ℕ)).map
      (IncomingMap.map f n V' F hF K L b) :=
  IncomingMap.reindex f n V' F hF K L b r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindexSteps
