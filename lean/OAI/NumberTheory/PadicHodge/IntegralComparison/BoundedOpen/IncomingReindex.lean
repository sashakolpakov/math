import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindexSteps

/-! # Incoming Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindex

noncomputable section

/-! Compose the checked changes of ambient open, family, and index
for the actual incoming comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private structure ComparisonData (C : Type*) [Category C] where
  A : C
  B : C
  D : C
  E : C
  a : A ⟶ B
  a' : A ⟶ B
  s : B ⟶ E
  t : A ⟶ D
  b : D ⟶ E
  b' : D ⟶ E
  ha : a = a'
  hb : a' ≫ s = t ≫ b
  hc : b = b'

private theorem ComparisonData.comparison {C : Type*} [Category C] (d : ComparisonData C) :
    d.a ≫ d.s = d.t ≫ d.b' := IncomingReindexSteps.compose_three d.ha d.hb d.hc

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

local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap.familyIso (p := p) (J := J) (δ := δ)
  f n G (IncomingMap.reindexedOpens F r) h

private def steps :=
  ComparisonData.mk
    (C := CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
    _ _ _ _ _ _ _ _ _ _
    (IncomingReindexSteps.open_step f n V V' hV G hG K L b)
    (IncomingReindexSteps.family_step f n V V' hV F G r hF hG h K L b)
    (IncomingReindexSteps.reindex_step f n V' F r hF K L b)

abbrev comparison :=
  (ComparisonData.comparison (steps f n V V' hV F G r hF hG h K L b))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindex
