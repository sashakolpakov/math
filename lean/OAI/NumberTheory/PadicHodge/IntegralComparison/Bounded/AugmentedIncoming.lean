import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.FromIncomingSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindex

/-! # Augmented Incoming -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.AugmentedIncoming.Comparison

noncomputable section

/-! Assemble the original incoming section-family square before
substituting smooth models or their coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (V V' : Y.Opens) (hV : V = V')
  {D : Type v} [Preorder D] {E : Type w} [Preorder E] [HasFiniteProducts E]
  [HasProducts.{w} (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))]
  (F : D →o Y.Opens) (G : E →o Y.Opens) (r : E ⥤ D)
  (hF : ∀ d, F d ≤ V') (hG : ∀ e, G e ≤ V)
  (h : G = BoundedOpen.IncomingMap.reindexedOpens F r)
  (K L : CochainComplex
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ)
  (b : ((BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj L)

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindexSteps.restriction (B := B) r
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n G
local notation "S₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n F
local notation "s" => NatIso.mapHomologicalComplex
  (BoundedOpen.IncomingMap.familyIso (p := p) (J := J) (δ := δ)
    f n G (BoundedOpen.IncomingMap.reindexedOpens F r) h) (ComplexShape.up ℕ)

private def targetIso : ((S₁).mapHomologicalComplex (.up ℕ)).obj L ≅
    ((H).mapHomologicalComplex (.up ℕ)).obj (((S₂).mapHomologicalComplex (.up ℕ)).obj L) :=
  ((s).app L)

private def sourceMap : ((S₁).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((H).mapHomologicalComplex (.up ℕ)).obj (((S₂).mapHomologicalComplex (.up ℕ)).obj K) :=
  ((s).app K).hom

private def leftMap : ((S₁).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((H).mapHomologicalComplex (.up ℕ)).obj (((S₂).mapHomologicalComplex (.up ℕ)).obj L) :=
  BoundedOpen.IncomingMap.map f n V G hG K L
    (BoundedOpen.IncomingMap.transport f n V K L V' hV b) ≫ ((s).app L).hom

private def rightMap : ((S₁).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((H).mapHomologicalComplex (.up ℕ)).obj (((S₂).mapHomologicalComplex (.up ℕ)).obj L) :=
  ((s).app K).hom ≫ ((H).mapHomologicalComplex (.up ℕ)).map
    (BoundedOpen.IncomingMap.map f n V' F hF K L b)

omit [HasFiniteProducts E]
  [HasProducts.{w} (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))] in
private theorem incomingComponent (q : ℕ) (d : Eᵒᵖ) :
    ((leftMap f n V V' hV F G r hG h K L b).f q).app d =
      ((rightMap f n V' F G r hF h K L b).f q).app d := by
  subst V'
  subst G
  change ((BoundedOpen.IncomingMap.map f n V
      (BoundedOpen.IncomingMap.reindexedOpens F r) hG K L b).f q).app d ≫ 𝟙 _ =
    𝟙 _ ≫ ((BoundedOpen.IncomingMap.map f n V F hF K L b).f q).app (r.op.obj d)
  rw [Category.comp_id, Category.id_comp]
  exact BoundedOpen.IncomingMap.reindex_component f n V F hF K L b r q d

omit [HasFiniteProducts E]
  [HasProducts.{w} (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))] in
private theorem incomingDegree (q : ℕ) :
    (leftMap f n V V' hV F G r hG h K L b).f q =
      (rightMap f n V' F G r hF h K L b).f q := by
  apply NatTrans.ext
  funext d
  exact incomingComponent f n V V' hV F G r hF hG h K L b q d

private abbrev incomingSquare :=
  HomologicalComplex.hom_ext
    (leftMap f n V V' hV F G r hG h K L b)
    (rightMap f n V' F G r hF h K L b)
    (incomingDegree f n V V' hV F G r hF hG h K L b)

private abbrev preparedComparison := AugmentedCech.FromIncomingSquare.comparison
  (B := ((S₁).mapHomologicalComplex (.up ℕ)).obj K)
  (I := ((S₁).mapHomologicalComplex (.up ℕ)).obj L)
  (B' := ((S₂).mapHomologicalComplex (.up ℕ)).obj K)
  (I' := ((S₂).mapHomologicalComplex (.up ℕ)).obj L)
  ((H).mapHomologicalComplex (.up ℕ)) (targetIso f n F G r h L)
  (BoundedOpen.IncomingMap.map f n V G hG K L
    (BoundedOpen.IncomingMap.transport f n V K L V' hV b))
  (BoundedOpen.IncomingMap.map f n V' F hF K L b)
  (sourceMap f n F G r h K)

abbrev comparison := preparedComparison f n V V' hV F G r hF hG h K L b
  (incomingSquare f n V V' hV F G r hF hG h K L b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.AugmentedIncoming.Comparison
