import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback

/-! # Pullback Section Congr -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr

noncomputable section

/-! Actual section pullback is compatible with a commuting square, with
independently chosen smaller opens on its four corners. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.PullbackSectionSquare

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections

theorem congr {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app V (RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hf s) =
      RestrictedPullback.Construction.RestrictedPullbackSections.map g M U V hg s := by
  subst g
  rfl

theorem comp_inv {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ g ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp g f).inv.app M).app W
      (RestrictedPullback.Construction.RestrictedPullbackSections.map (g ≫ f) M U W (fun _ hz => hVU (hWV hz)) s) =
        RestrictedPullback.Construction.RestrictedPullbackSections.map g ((Scheme.Modules.pullback f).obj M) V W hWV (RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hVU s) := by
  have hc := RestrictedPullback.Construction.RestrictedPullbackSections.comp f g M U V W hVU hWV s
  have he := congrArg (((Scheme.Modules.pullbackComp g f).inv.app M).app W) hc.symm
  exact he.trans (congrArg (fun a : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M) =>
        a.app W (RestrictedPullback.Construction.RestrictedPullbackSections.map g ((Scheme.Modules.pullback f).obj M) V W hWV (RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hVU s)))
    ((Scheme.Modules.pullbackComp g f).app M).hom_inv_id)

variable {X Y X' Y' : Scheme.{u}}
variable (i : Y ⟶ X) (p : X' ⟶ X) (q : Y' ⟶ Y) (j : Y' ⟶ X')
variable (h : q ≫ i = j ≫ p) (M : X.Modules)

def iso : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback i).obj M) ≅
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackComp q i).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp j p).app M).symm

theorem apply (U : X.Opens) (V : Y.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hi : V ≤ i ⁻¹ᵁ U) (hp : U' ≤ p ⁻¹ᵁ U) (hq : V' ≤ q ⁻¹ᵁ V) (hj : V' ≤ j ⁻¹ᵁ U')
    (s : Γ(M, U)) :
    (iso i p q j h M).hom.app V'
      (RestrictedPullback.Construction.RestrictedPullbackSections.map q ((Scheme.Modules.pullback i).obj M) V V' hq (RestrictedPullback.Construction.RestrictedPullbackSections.map i M U V hi s)) =
        RestrictedPullback.Construction.RestrictedPullbackSections.map j ((Scheme.Modules.pullback p).obj M) U' V' hj (RestrictedPullback.Construction.RestrictedPullbackSections.map p M U U' hp s) := by
  change ((Scheme.Modules.pullbackComp j p).inv.app M).app V'
    (((Scheme.Modules.pullbackCongr h).hom.app M).app V'
      (((Scheme.Modules.pullbackComp q i).hom.app M).app V'
        (RestrictedPullback.Construction.RestrictedPullbackSections.map q ((Scheme.Modules.pullback i).obj M) V V' hq (RestrictedPullback.Construction.RestrictedPullbackSections.map i M U V hi s)))) = _
  rw [RestrictedPullback.Construction.RestrictedPullbackSections.comp]
  have hc := congr h M U V' (fun _ hy => hi (hq hy)) (fun _ hy => hp (hj hy)) s
  exact (congrArg (((Scheme.Modules.pullbackComp j p).inv.app M).app V') hc).trans
    (comp_inv p j M U U' V' hp hj s)

theorem vertical (U : X.Opens) (V : Y.Opens) (hi : V ≤ i ⁻¹ᵁ U)
    (hj : q ⁻¹ᵁ V ≤ j ⁻¹ᵁ (p ⁻¹ᵁ U)) (s : Γ(M, U)) :
    (iso i p q j h M).hom.app (q ⁻¹ᵁ V)
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map q ((Scheme.Modules.pullback i).obj M) V
        (RestrictedPullback.Construction.RestrictedPullbackSections.map i M U V hi s)) =
      RestrictedPullback.Construction.RestrictedPullbackSections.map j ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (q ⁻¹ᵁ V) hj
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map p M U s) := by
  simpa only [RestrictedPullback.Construction.RestrictedPullbackSections.full] using
    apply i p q j h M U V (p ⁻¹ᵁ U) (q ⁻¹ᵁ V) hi le_rfl le_rfl hj s

end Construction.PullbackSectionSquare

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr
