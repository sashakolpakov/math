import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestriction

/-! # Sections Localized Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsLocalizedExtension

noncomputable section

/-! If a smaller open meets the larger support only in a closed section,
local supported classes extend through that section into the larger
support. The extension is a section of restriction and is natural in
the coefficient complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

def codomainIso (U V W : Opens X) (hV : V ≤ U) (hW : W ≤ U) (e : V = W) :
    SectionsExcision.supported (D := D) U V hV ≅ SectionsExcision.supported U W hW := by
  subst W
  exact Iso.refl _

theorem codomainIso_inclusion (U V W : Opens X) (hV : V ≤ U) (hW : W ≤ U) (e : V = W)
    (F : Sheaf (Opens.grothendieckTopology X) D) :
    (codomainIso U V W hV hW e).hom.app F ≫ (SectionsExcision.inclusion U W hW).app F =
      (SectionsExcision.inclusion U V hV).app F := by
  subst W
  exact Category.id_comp _

def enlarge (O₁ O₂ : Opens X) (h : O₁ ≤ O₂) :
    SectionsExcision.supported (D := D) ⊤ O₂ le_top ⟶ SectionsExcision.supported ⊤ O₁ le_top where
  app F := kernel.map _ _ (𝟙 ((SectionsExcision.sections ⊤).obj F)) ((SectionsExcision.restriction O₂ O₁ h).app F) (by
    rw [Category.id_comp]
    change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
    rw [← F.obj.map_comp]
    congr 1)
  naturality F G f := by
    apply (cancel_mono (kernel.ι ((SectionsExcision.restriction ⊤ O₁ le_top).app G))).mp
    simp only [SectionsExcision.supported, kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc,
      Category.comp_id]

theorem enlarge_inclusion (O₁ O₂ : Opens X) (h : O₁ ≤ O₂)
    (F : Sheaf (Opens.grothendieckTopology X) D) :
    (enlarge O₁ O₂ h).app F ≫ (SectionsExcision.inclusion ⊤ O₁ le_top).app F =
      (SectionsExcision.inclusion ⊤ O₂ le_top).app F := by
  exact (kernel.lift_ι _ _ _).trans (Category.comp_id _)

variable (O₁ O₂ V : Opens X) (h : O₁ ≤ O₂)
  (he : V ⊓ O₁ = V ⊓ O₂) (hc : V ⊔ O₂ = ⊤)

def localIso : SectionsExcision.supported (D := D) V (V ⊓ O₁) inf_le_left ≅
    SectionsExcision.supported V (V ⊓ O₂) inf_le_left :=
  codomainIso V (V ⊓ O₁) (V ⊓ O₂) inf_le_left inf_le_left he

def toSection : SectionsExcision.supported (D := D) V (V ⊓ O₁) inf_le_left ⟶ SectionsExcision.supported ⊤ O₂ le_top :=
  (localIso O₁ O₂ V he).hom ≫ (SectionsExcision.excisionIso O₂ V hc).inv

def lift : SectionsExcision.supported (D := D) V (V ⊓ O₁) inf_le_left ⟶ SectionsExcision.supported ⊤ O₁ le_top :=
  toSection O₁ O₂ V he hc ≫ enlarge O₁ O₂ h

theorem lift_inclusion (F : Sheaf (Opens.grothendieckTopology X) D) :
    (lift O₁ O₂ V h he hc).app F ≫ (SectionsExcision.inclusion ⊤ O₁ le_top).app F =
      (localIso O₁ O₂ V he).hom.app F ≫ (SectionsExcision.extension O₂ V hc).app F := by
  change (((localIso O₁ O₂ V he).hom.app F ≫ (SectionsExcision.excisionIso O₂ V hc).inv.app F) ≫
      (enlarge O₁ O₂ h).app F) ≫ (SectionsExcision.inclusion ⊤ O₁ le_top).app F = _
  rw [Category.assoc, Category.assoc, enlarge_inclusion]
  rfl

theorem lift_restriction : lift (D := D) O₁ O₂ V h he hc ≫ SectionsExcision.excision O₁ V = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  apply (cancel_mono (kernel.ι ((SectionsExcision.restriction V (V ⊓ O₁) inf_le_left).app F))).mp
  change ((lift O₁ O₂ V h he hc).app F ≫ (SectionsExcision.excision O₁ V).app F) ≫
      (SectionsExcision.inclusion V (V ⊓ O₁) inf_le_left).app F =
    𝟙 _ ≫ (SectionsExcision.inclusion V (V ⊓ O₁) inf_le_left).app F
  rw [Category.assoc, SectionsExcision.excision_inclusion, ← Category.assoc, lift_inclusion,
    Category.assoc, SectionsExcision.extension_restriction, Category.id_comp]
  exact codomainIso_inclusion V (V ⊓ O₁) (V ⊓ O₂) inf_le_left inf_le_left he F

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)

def localComplex := ((SectionsExcision.supported (D := D) V (V ⊓ O₁) inf_le_left).mapHomologicalComplex (.up ℕ)).obj K

def globalComplex := ((SectionsExcision.supported (D := D) ⊤ O₁ le_top).mapHomologicalComplex (.up ℕ)).obj K

def complex : localComplex O₁ V K ⟶ globalComplex O₁ K :=
  (NatTrans.mapHomologicalComplex (lift O₁ O₂ V h he hc) (.up ℕ)).app K

def restrictionComplex : globalComplex O₁ K ⟶ localComplex O₁ V K :=
  (NatTrans.mapHomologicalComplex (SectionsExcision.excision O₁ V) (.up ℕ)).app K

def toSectionComplex := (NatTrans.mapHomologicalComplex (toSection O₁ O₂ V he hc) (.up ℕ)).app K

theorem complex_restriction : complex O₁ O₂ V h he hc K ≫ restrictionComplex O₁ V K = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun a => a.app (K.X n)) (lift_restriction (D := D) O₁ O₂ V h he hc)

theorem complex_inclusion :
    complex O₁ O₂ V h he hc K ≫
        (NatTrans.mapHomologicalComplex (SectionsExcision.inclusion ⊤ O₁ le_top) (.up ℕ)).app K =
      toSectionComplex O₁ O₂ V he hc K ≫
        (NatTrans.mapHomologicalComplex (SectionsExcision.inclusion ⊤ O₂ le_top) (.up ℕ)).app K := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((toSection O₁ O₂ V he hc).app (K.X n) ≫ (enlarge O₁ O₂ h).app (K.X n)) ≫
    (SectionsExcision.inclusion ⊤ O₁ le_top).app (K.X n) = _
  rw [Category.assoc, enlarge_inclusion]
  rfl

theorem complex_natural {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ}
    (a : K ⟶ L) :
    ((SectionsExcision.supported V (V ⊓ O₁) inf_le_left).mapHomologicalComplex (.up ℕ)).map a ≫
        complex O₁ O₂ V h he hc L =
      complex O₁ O₂ V h he hc K ≫
        ((SectionsExcision.supported ⊤ O₁ le_top).mapHomologicalComplex (.up ℕ)).map a :=
  (NatTrans.mapHomologicalComplex (lift O₁ O₂ V h he hc) (.up ℕ)).naturality a

theorem homology_restriction (n : ℕ) :
    HomologicalComplex.homologyMap (complex O₁ O₂ V h he hc K) n ≫
      HomologicalComplex.homologyMap (restrictionComplex O₁ V K) n = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp, complex_restriction, HomologicalComplex.homologyMap_id]

theorem homology_natural {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ}
    (a : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((SectionsExcision.supported V (V ⊓ O₁) inf_le_left).mapHomologicalComplex (.up ℕ)).map a) n ≫
        HomologicalComplex.homologyMap (complex O₁ O₂ V h he hc L) n =
      HomologicalComplex.homologyMap (complex O₁ O₂ V h he hc K) n ≫
        HomologicalComplex.homologyMap
          (((SectionsExcision.supported ⊤ O₁ le_top).mapHomologicalComplex (.up ℕ)).map a) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (complex_natural O₁ O₂ V h he hc K a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsLocalizedExtension
