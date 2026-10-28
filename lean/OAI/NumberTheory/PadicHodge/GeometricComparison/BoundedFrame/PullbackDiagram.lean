import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Pullback Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagram.BoundedFramePullbackDiagram

noncomputable section

/-! A geometric map and an actual frame morphism induce a map of the native
bounded product diagrams. The geometric map need not be a monomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n

variable (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

def sourceDiagram : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ IntegralComparison.BigCrystallineSite.Object p B J δ fY :=
  IntegralComparison.BoundedFrame.Diagram.productDiagram FX ⋙ T

def targetDiagram : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ IntegralComparison.BigCrystallineSite.Object p B J δ fY :=
  G ⋙ IntegralComparison.BoundedFrame.Diagram.productDiagram FY

def comparison : sourceDiagram g hg n FX ⟶ targetDiagram g hg n FY where
  app U := (QY).map (prod.lift ((G).map (prod.fst : FX ⨯ U ⟶ FX) ≫ α) ((G).map prod.snd))
  naturality U V β := by
    change (QY).map ((G).map (prod.map (𝟙 FX) β)) ≫
        (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) =
      (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) ≫
        (QY).map (prod.map (𝟙 FY) ((G).map β))
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (QY).map
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
      rw [← Category.assoc, ← Functor.map_comp, prod.map_fst, Category.comp_id]
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp, prod.map_snd]

def sourceProjection : sourceDiagram g hg n FX ⟶ G ⋙ QY :=
  Functor.whiskerRight (IntegralComparison.BoundedFrame.Diagram.projection FX) T

def targetProjection : targetDiagram g hg n FY ⟶ G ⋙ QY :=
  Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Diagram.projection FY)

theorem projection : comparison g hg n FX FY α ≫ targetProjection g hg n FY =
    sourceProjection g hg n FX := by
  apply NatTrans.ext
  funext U
  change (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) ≫
      (IntegralComparison.BoundedFrame.Diagram.projection FY).app ((G).obj U) =
    (T).map ((IntegralComparison.BoundedFrame.Diagram.projection FX).app U)
  rw [IntegralComparison.BoundedFrame.Diagram.projection_app, IntegralComparison.BoundedFrame.Diagram.projection_app]
  change (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) ≫
    (QY).map prod.snd = (QY).map ((G).map prod.snd)
  rw [← Functor.map_comp, prod.lift_snd]

def sourceFrameProjection : sourceDiagram g hg n FX ⟶ (Functor.const _).obj ((G).obj FX).obj :=
  Functor.whiskerRight (IntegralComparison.BoundedFrame.Symbols.frameProjection FX) T

def targetFrameProjection : targetDiagram g hg n FY ⟶ (Functor.const _).obj FY.obj :=
  Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Symbols.frameProjection FY)

theorem frameProjection : comparison g hg n FX FY α ≫ targetFrameProjection g hg n FY =
    sourceFrameProjection g hg n FX ≫ (Functor.const _).map ((QY).map α) := by
  apply NatTrans.ext
  funext U
  change (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) ≫
      (IntegralComparison.BoundedFrame.Symbols.frameProjection FY).app ((G).obj U) =
    (T).map ((IntegralComparison.BoundedFrame.Symbols.frameProjection FX).app U) ≫ (QY).map α
  rw [IntegralComparison.BoundedFrame.Symbols.frameProjection_app, IntegralComparison.BoundedFrame.Symbols.frameProjection_app]
  change (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) ≫
    (QY).map prod.fst = (QY).map ((G).map prod.fst) ≫ (QY).map α
  rw [← Functor.map_comp, prod.lift_fst, Functor.map_comp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagram.BoundedFramePullbackDiagram
