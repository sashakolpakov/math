import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality

/-! # Restricted Section Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.RestrictedSectionComposition

noncomputable section

/-! Composition and commutative-square comparisons preserve section values pulled back to arbitrary smaller opens. This version allows local sections, so it applies to parameter charts without a global extension of the section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def pullbackSectionValueOn {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (x : Γ(M, U)) :
    Γ((Scheme.Modules.pullback f).obj M, W) :=
  ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hW).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U x)

theorem pullbackSectionValueOn_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) (U : Y.Opens) (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) (x : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app W
        (pullbackSectionValueOn f M U W hf x) =
      pullbackSectionValueOn g M U W hg x := by
  subst g
  rfl

theorem pullbackSectionValueOn_comp {X Y Z : Scheme.{u}} (a : Z ⟶ Y) (j : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (hV : V ≤ j ⁻¹ᵁ U) (hW : W ≤ a ⁻¹ᵁ V)
    (hWU : W ≤ (a ≫ j) ⁻¹ᵁ U) (x : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp a j).hom.app M).app W
      (pullbackSectionValueOn a ((Scheme.Modules.pullback j).obj M) V W hW
        (pullbackSectionValueOn j M U V hV x)) =
      pullbackSectionValueOn (a ≫ j) M U W hWU x := by
  let N := (Scheme.Modules.pullback j).obj M
  let P := (Scheme.Modules.pullback a).obj N
  let Q := (Scheme.Modules.pullback (a ≫ j)).obj M
  let u : N ⟶ (Scheme.Modules.pushforward a).obj P :=
    (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app N
  let s : Γ(N, j ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app U x
  let t : Γ(P, (Opens.map a.base).obj (j ⁻¹ᵁ U)) := u.app (j ⁻¹ᵁ U) s
  let e : P ⟶ Q := (Scheme.Modules.pullbackComp a j).hom.app M
  have hWU' : W ≤ (Opens.map a.base).obj (j ⁻¹ᵁ U) := hWU
  have hn := ConcreteCategory.congr_hom (u.mapPresheaf.naturality (homOfLE hV).op) s
  change u.app V (N.presheaf.map (homOfLE hV).op s) =
    P.presheaf.map ((Opens.map a.base).map (homOfLE hV)).op t at hn
  have hr : P.presheaf.map (homOfLE hW).op
      (P.presheaf.map ((Opens.map a.base).map (homOfLE hV)).op t) =
    P.presheaf.map (homOfLE hWU').op t := by
    rw [← P.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom (P.presheaf.congr_map (Subsingleton.elim _ _)) t
  change e.app W (P.presheaf.map (homOfLE hW).op
      (u.app V (N.presheaf.map (homOfLE hV).op s))) = _
  rw [hn, hr]
  have he := ConcreteCategory.congr_hom (e.mapPresheaf.naturality (homOfLE hWU').op) t
  exact he.trans (congrArg (Q.presheaf.map (homOfLE hWU').op)
    (UnitCompositionValues.pullbackUnit_comp_value a j M U x))

theorem modulePullbackSquareIso_restricted_section
    {X X' Y Y' : Scheme.{u}} (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) (M : X.Modules)
    (U : X.Opens) (V : X'.Opens) (V' : Y.Opens) (W : Y'.Opens)
    (hV : V ≤ a ⁻¹ᵁ U) (hV' : V' ≤ f ⁻¹ᵁ U)
    (hW : W ≤ g ⁻¹ᵁ V) (hW' : W ≤ b ⁻¹ᵁ V') (x : Γ(M, U)) :
    ((SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M).app W
      (pullbackSectionValueOn g ((Scheme.Modules.pullback a).obj M) V W hW
        (pullbackSectionValueOn a M U V hV x)) =
    pullbackSectionValueOn b ((Scheme.Modules.pullback f).obj M) V' W hW'
      (pullbackSectionValueOn f M U V' hV' x) := by
  let hg : W ≤ (g ≫ a) ⁻¹ᵁ U :=
    hW.trans (leOfHom ((Opens.map g.base).map (homOfLE hV)))
  let hb : W ≤ (b ≫ f) ⁻¹ᵁ U :=
    hW'.trans (leOfHom ((Opens.map b.base).map (homOfLE hV')))
  let P := (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M)
  let s : Γ(P, W) := pullbackSectionValueOn g ((Scheme.Modules.pullback a).obj M) V W hW
    (pullbackSectionValueOn a M U V hV x)
  change ((Scheme.Modules.pullbackComp b f).inv.app M).app W
      (((Scheme.Modules.pullbackCongr h).hom.app M).app W
        (((Scheme.Modules.pullbackComp g a).hom.app M).app W s)) = _
  dsimp only [s]
  rw [pullbackSectionValueOn_comp g a M U V W hV hW hg x,
    pullbackSectionValueOn_congr h M U W hg hb x,
    ← pullbackSectionValueOn_comp b f M U V' W hV' hW' hb x]
  let Q := (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback f).obj M)
  let s : Γ(Q, W) := pullbackSectionValueOn b ((Scheme.Modules.pullback f).obj M) V' W hW'
    (pullbackSectionValueOn f M U V' hV' x)
  exact congrArg (fun e : Q ⟶ Q => e.app W s) ((Scheme.Modules.pullbackComp b f).app M).hom_inv_id

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.RestrictedSectionComposition
