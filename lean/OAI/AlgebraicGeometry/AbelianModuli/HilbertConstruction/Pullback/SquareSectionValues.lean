import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues

/-! # Square Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareSectionValues

noncomputable section

/-! The canonical comparison across a commutative square preserves actual pulled-back global sections, including their restrictions to inverse-image opens. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem pullbackUnit_congr_top {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x) =
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ x := by
  subst g
  rfl

theorem pullbackUnit_restrict_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (V : Y.Opens) (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V
        (M.presheaf.map V.leTop.op x) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map (f ⁻¹ᵁ V).leTop.op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x) := by
  exact ConcreteCategory.congr_hom
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
      V.leTop.op) x

variable {X X' Y Y' : Scheme.{u}}
variable (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
variable (h : g ≫ a = b ≫ f) (M : X.Modules)

theorem modulePullbackSquareIso_unit_top (x : Γ(M, ⊤)) :
    ((SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pullback a).obj M)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
        ((Scheme.Modules.pullback f).obj M)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x) := by
  let Ma : X'.Modules := (Scheme.Modules.pullback a).obj M
  let Mf : Y.Modules := (Scheme.Modules.pullback f).obj M
  let Mag : Y'.Modules := (Scheme.Modules.pullback g).obj Ma
  let Mfb : Y'.Modules := (Scheme.Modules.pullback b).obj Mf
  let Mga : Y'.Modules := (Scheme.Modules.pullback (g ≫ a)).obj M
  let Mbf : Y'.Modules := (Scheme.Modules.pullback (b ≫ f)).obj M
  let sa : Γ(Ma, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x
  let sf : Γ(Mf, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x
  let sag : Γ(Mag, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Ma).app ⊤ sa
  let sfb : Γ(Mfb, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app Mf).app ⊤ sf
  let sga : Γ(Mga, ⊤) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ a)).unit.app M).app ⊤ x
  let sbf : Γ(Mbf, ⊤) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (b ≫ f)).unit.app M).app ⊤ x
  let u : Mag ⟶ Mga := (Scheme.Modules.pullbackComp g a).hom.app M
  let v : Mga ⟶ Mbf := (Scheme.Modules.pullbackCongr h).hom.app M
  let w : Mbf ⟶ Mfb := (Scheme.Modules.pullbackComp b f).inv.app M
  let w' : Mfb ⟶ Mbf := (Scheme.Modules.pullbackComp b f).hom.app M
  have hu : u.app ⊤ sag = sga := UnitCompositionValues.pullbackUnit_comp_value g a M ⊤ x
  have hv : v.app ⊤ sga = sbf := pullbackUnit_congr_top h M x
  have hw' : w'.app ⊤ sfb = sbf := UnitCompositionValues.pullbackUnit_comp_value b f M ⊤ x
  have hid : w.app ⊤ (w'.app ⊤ sfb) = sfb :=
    congrArg (fun e : Mfb ⟶ Mfb => e.app ⊤ sfb)
      ((Scheme.Modules.pullbackComp b f).app M).hom_inv_id
  have hw : w.app ⊤ sbf = sfb := (congrArg (w.app ⊤) hw').symm.trans hid
  exact (congrArg (fun t : Γ(Mga, ⊤) => w.app ⊤ (v.app ⊤ t)) hu).trans
    ((congrArg (w.app ⊤) hv).trans hw)

theorem modulePullbackSquareIso_unit_restrict (V : X'.Opens) (x : Γ(M, ⊤)) :
    ((SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M).app (g ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pullback a).obj M)).app V
          (((Scheme.Modules.pullback a).obj M).presheaf.map V.leTop.op
            (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x))) =
      ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback f).obj M)).presheaf.map
        (g ⁻¹ᵁ V).leTop.op
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
            ((Scheme.Modules.pullback f).obj M)).app ⊤
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ x)) := by
  let Ma : X'.Modules := (Scheme.Modules.pullback a).obj M
  let Mag : Y'.Modules := (Scheme.Modules.pullback g).obj Ma
  let Mfb : Y'.Modules := (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback f).obj M)
  let e : Mag ⟶ Mfb := (SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M
  let t : Γ(Ma, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x
  let s : Γ(Mag, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Ma).app ⊤ t
  have hr : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Ma).app V
      (Ma.presheaf.map V.leTop.op t) = Mag.presheaf.map (g ⁻¹ᵁ V).leTop.op s :=
    pullbackUnit_restrict_top g Ma V t
  have hn := ConcreteCategory.congr_hom (e.mapPresheaf.naturality (g ⁻¹ᵁ V).leTop.op) s
  exact (congrArg (e.app (g ⁻¹ᵁ V)) hr).trans (hn.trans
    (congrArg (Mfb.presheaf.map (g ⁻¹ᵁ V).leTop.op)
      (modulePullbackSquareIso_unit_top a b f g h M x)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareSectionValues
