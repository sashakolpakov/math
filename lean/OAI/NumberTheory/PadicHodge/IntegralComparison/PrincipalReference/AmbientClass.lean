import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SupportedClass

/-! # Ambient Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.AmbientClass.Reference

noncomputable section

/-! The original localized point class forgets to a fixed ambient
class. Its value is independent of the chosen punctured principal cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : A ⟶ F)
    (e : F ⟶ G) (f : G ⟶ E) (g : B ⟶ G)
    (hb : b ≫ c = g ≫ f) (ha : a ≫ g = d ≫ e) :
    (a ≫ b) ≫ c = d ≫ (e ≫ f) := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

private theorem inverse_square {C : Type*} [Category C] {T S A B D : C}
    (e : S ≅ A) (h : B ≅ D) (l : T ⟶ A) (f : S ⟶ B) (g : A ⟶ D) (r : T ⟶ D)
    (he : e.hom ≫ g = f ≫ h.hom) (hl : l ≫ g = r) :
    (l ≫ e.inv) ≫ f = r ≫ h.inv := by
  apply (cancel_mono h.hom).mp
  calc
    _ = l ≫ e.inv ≫ (f ≫ h.hom) := by simp only [Category.assoc]
    _ = l ≫ e.inv ≫ (e.hom ≫ g) := by rw [he]
    _ = l ≫ g := by simp only [Iso.inv_hom_id_assoc]
    _ = r := hl
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

 def ambientIso (q : ℕ) :=
  (Principal.AdditiveSections.forgetScalars U).mapIso (Concentration.Reference.ambientIso U hU K c hK q) ≪≫
    Principal.SingleAdditiveForget.ambientHomologyIso U hU (K.homology c) c q

 def ambient (q : ℕ) :=
  homologyMap (Supported.ZeroComplementComplex.restrictionMap
    (Principal.ClosedSingleSupport.terminalOpen U hU) (Principal.SingleAdditiveSections.sheafSingle (K.homology c) c)) q ≫
      (ambientIso U hU K c hK q).inv

variable {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U)

 theorem concentration_square (q : ℕ) :
    (SupportedClass.Reference.concentratedIso U hU W K c hK q).hom ≫
      homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.SingleAdditiveSections.sheafDiagram U hU (K.homology c) c)) q =
    (Principal.AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.AdditiveSections.linearComplex U hU K)) q) ≫
      (ambientIso U hU K c hK q).hom := by
  have h := congrArg ((Principal.AdditiveSections.forgetScalars U).map)
    (Concentration.Reference.square U hU W K c hK q)
  simp only [Functor.map_comp] at h
  exact paste
    ((Principal.AdditiveSections.forgetScalars U).map (Concentration.Reference.iso U hU W K c hK q).hom)
    (Principal.SingleAdditiveSections.homologyIso U hU (K.homology c) c W q).hom
    (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.SingleAdditiveSections.sheafDiagram U hU (K.homology c) c)) q)
    ((Principal.AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.AdditiveSections.linearComplex U hU K)) q))
    ((Principal.AdditiveSections.forgetScalars U).map (Concentration.Reference.ambientIso U hU K c hK q).hom)
    (Principal.SingleAdditiveForget.ambientHomologyIso U hU (K.homology c) c q).hom
    ((Principal.AdditiveSections.forgetScalars U).map
      (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.AdditiveSections.linearComplex U hU (Principal.SingleAdditiveSections.moduleSingle (K.homology c) c))) q))
    (Principal.SingleAdditiveForget.homology U hU (K.homology c) c W q) h

variable {Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
  (N : Z.Modules) (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hW : ∀ i, Principal.SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)

 theorem localize_forget (q : ℕ) :
    SupportedClass.Reference.localize U hU W K c hK f N e hW q ≫
      (Principal.AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.AdditiveSections.linearComplex U hU K)) q) =
    ambient U hU K c hK q := by
  have hl := congrArg (fun a => homologyMap a q)
    (Principal.ClosedSingleSupport.forget_normalization f N (K.homology c) e U hU W hW c)
  simp only [homologyMap_comp] at hl
  exact inverse_square
    (SupportedClass.Reference.concentratedIso U hU W K c hK q)
    (ambientIso U hU K c hK q)
    (homologyMap (Principal.ClosedSingleSupport.toPrincipal f N (K.homology c) e U hU W hW c) q)
    ((Principal.AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.AdditiveSections.linearComplex U hU K)) q))
    (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.SingleAdditiveSections.sheafDiagram U hU (K.homology c) c)) q)
    (homologyMap (Supported.ZeroComplementComplex.restrictionMap
      (Principal.ClosedSingleSupport.terminalOpen U hU) (Principal.SingleAdditiveSections.sheafSingle (K.homology c) c)) q)
    (concentration_square U hU K c hK W q)
    (by simpa only [Principal.ClosedSingleSupport.toPrincipal,
      Closed.SupportedSurvivor.lift, homologyMap_comp] using hl)

variable {κ : Type u} [LinearOrder κ] (V : κ → Principal.SectionPresheaf.Index U)
  (hV : ∀ i, Principal.SectionPresheaf.openSubset U (V i) ≤ SectionIdealPuncturedCover.outside f.ker)

 theorem independent (q : ℕ) :
    SupportedClass.Reference.localize U hU W K c hK f N e hW q ≫
      (Principal.AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport W (Principal.AdditiveSections.linearComplex U hU K)) q) =
    SupportedClass.Reference.localize U hU V K c hK f N e hV q ≫
      (Principal.AdditiveSections.forgetScalars U).map (homologyMap (AugmentedOrdered.CechForget.forgetSupport V (Principal.AdditiveSections.linearComplex U hU K)) q) :=
  (localize_forget U hU K c hK W f N e hW q).trans
    (localize_forget U hU K c hK V f N e hV q).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.AmbientClass.Reference
