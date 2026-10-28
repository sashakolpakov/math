import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts

/-! # Product Preservation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ProductPreservation

noncomputable section

/-!
# IntegralComparison: fully faithful functors with incoming lifts preserve binary products

An incoming product cone lifts through its first leg. Fullness lifts its
second leg, and the original product universal property then supplies
the unique map. This applies to crystalline restriction along monomorphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [F.Full] [F.Faithful] (L : SiteLifts.IncomingLifts F)
  {U V : C}

def sourceFan (s : BinaryFan (F.obj U) (F.obj V)) : BinaryFan U V :=
  BinaryFan.mk (L.hom s.fst) (F.preimage ((L.iso s.fst).hom ≫ s.snd))

variable (c : BinaryFan U V) (hc : IsLimit c)

def lift (s : BinaryFan (F.obj U) (F.obj V)) : s.pt ⟶ F.obj c.pt :=
  (L.iso s.fst).inv ≫ F.map (hc.lift (sourceFan F L s))

omit [F.Faithful] in
theorem lift_fst (s : BinaryFan (F.obj U) (F.obj V)) :
    ProductPreservation.lift F L c hc s ≫ F.map c.fst = s.fst := by
  erw [ProductPreservation.lift, Category.assoc, ← F.map_comp, hc.fac (sourceFan F L s) ⟨WalkingPair.left⟩]
  change (L.iso s.fst).inv ≫ F.map (L.hom s.fst) = s.fst
  erw [L.map_hom]
  exact (L.iso s.fst).inv_hom_id_assoc s.fst

omit [F.Faithful] in
theorem lift_snd (s : BinaryFan (F.obj U) (F.obj V)) :
    ProductPreservation.lift F L c hc s ≫ F.map c.snd = s.snd := by
  erw [ProductPreservation.lift, Category.assoc, ← F.map_comp, hc.fac (sourceFan F L s) ⟨WalkingPair.right⟩]
  change (L.iso s.fst).inv ≫ F.map (F.preimage ((L.iso s.fst).hom ≫ s.snd)) = s.snd
  erw [F.map_preimage]
  exact (L.iso s.fst).inv_hom_id_assoc s.snd

theorem lift_unique (s : BinaryFan (F.obj U) (F.obj V)) (m : s.pt ⟶ F.obj c.pt)
    (hfst : m ≫ F.map c.fst = s.fst) (hsnd : m ≫ F.map c.snd = s.snd) :
    m = ProductPreservation.lift F L c hc s := by
  have he : F.preimage ((L.iso s.fst).hom ≫ m) = hc.lift (sourceFan F L s) := by
    apply BinaryFan.IsLimit.hom_ext hc
    · erw [hc.fac (sourceFan F L s) ⟨WalkingPair.left⟩]
      apply F.map_injective
      change F.map (F.preimage ((L.iso s.fst).hom ≫ m) ≫ c.fst) = F.map (L.hom s.fst)
      erw [F.map_comp, F.map_preimage, Category.assoc, hfst, L.map_hom]
    · erw [hc.fac (sourceFan F L s) ⟨WalkingPair.right⟩]
      apply F.map_injective
      change F.map (F.preimage ((L.iso s.fst).hom ≫ m) ≫ c.snd) =
        F.map (F.preimage ((L.iso s.fst).hom ≫ s.snd))
      erw [F.map_comp, F.map_preimage, F.map_preimage, Category.assoc, hsnd]
  apply (cancel_epi (L.iso s.fst).hom).mp
  erw [ProductPreservation.lift, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (F.map_preimage ((L.iso s.fst).hom ≫ m)).symm.trans (congrArg (fun f => F.map f) he)

def isLimit : IsLimit (c.map F) :=
  BinaryFan.isLimitMk (ProductPreservation.lift F L c hc) (lift_fst F L c hc) (lift_snd F L c hc)
    (lift_unique F L c hc)

def isLimitMapCone : IsLimit (F.mapCone c) :=
  (BinaryFan.isLimitMapConeEquiv (F := F)).symm (isLimit F L c hc)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ProductPreservation
