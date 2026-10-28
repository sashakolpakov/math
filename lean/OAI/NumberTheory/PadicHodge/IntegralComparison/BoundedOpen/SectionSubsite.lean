import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionSubsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex

/-! # Section Subsite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite

noncomputable section

/-! Original bounded crystalline sections over opens inside one fixed
open are sections of the restricted crystalline sheaf, naturally in
the whole family of opens and in the coefficient sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (V : Y.Opens) {D : Type v} [Preorder D] (F : D →o Y.Opens)
  (hF : ∀ d, F d ≤ V)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.property (p := p) (J := J) (δ := δ) fY V.ι n

def familyProperty (d : D) := SectionPresheaf.property
  (p := p) (J := J) (δ := δ) fY n (F d)

theorem family_monotone : Monotone (familyProperty (p := p) (J := J) (δ := δ) fY n F) := by
  intro a b hab
  exact SectionPresheaf.monotone fY n (F.monotone hab)

include hF in
theorem family_le (d : D) : familyProperty (p := p) (J := J) (δ := δ) fY n F d ≤ P :=
  SectionPresheaf.monotone fY n (hF d)

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.familyProperty (p := p) (J := J) (δ := δ) fY n F
local notation "hQ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.family_monotone (p := p) (J := J) (δ := δ) fY n F

def localSections : Subsite.ModuleSheaf
    (p := p) (J := J) (δ := δ) fY V.ι n ⥤ Dᵒᵖ ⥤ ModuleCat.{u + 2} R :=
  sheafToPresheaf (Subsite.topology fY V.ι n) (ModuleCat.{u + 1} R) ⋙
    Incoming.SectionPresheaf.functor R (ModuleCat.of R R)
      (Incoming.SectionSubsite.nested P Q) (Incoming.SectionSubsite.nested_monotone P Q hQ) ⋙
    (Functor.whiskeringRight Dᵒᵖ (ModuleCat.{u + 1} R) (ModuleCat.{u + 2} R)).obj
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R)

instance localSections_additive : (localSections (p := p) (J := J) (δ := δ) fY n V F).Additive := by
  dsimp only [localSections]
  infer_instance

def globalSections : BoundedCrystalline.Site.ModuleSheaf
    (p := p) (J := J) (δ := δ) fY n ⥤ Dᵒᵖ ⥤ ModuleCat.{u + 2} R :=
  SectionComplex.functor fY n ⋙
    (Functor.whiskeringLeft Dᵒᵖ Y.Opensᵒᵖ (ModuleCat.{u + 2} R)).obj F.toFunctor.op

instance globalSections_additive : (globalSections (p := p) (J := J) (δ := δ) fY n F).Additive := by
  dsimp only [globalSections]
  infer_instance

def iso : globalSections (p := p) (J := J) (δ := δ) fY n F ≅
    Subsite.restriction fY V.ι n ⋙ localSections fY n V F :=
  NatIso.ofComponents (fun M =>
    ((Functor.whiskeringRight Dᵒᵖ (ModuleCat.{u + 1} R) (ModuleCat.{u + 2} R)).obj
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R)).mapIso
        (Incoming.SectionSubsite.presheafIso R (ModuleCat.of R R) P Q hQ
          (family_le fY n V F hF) M.obj)) (by
    intro M N a
    apply NatTrans.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply NatTrans.ext
    funext T
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite
