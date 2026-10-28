import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

/-! # General Frame Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.GeneralFrameComparison

noncomputable section

/-!
# IntegralComparison: native bounded frame product diagrams have comparison maps for arbitrary geometric maps
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg

def sourceDiagram : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ BigCrystallineSite.Object p B J δ fY :=
  BoundedFrame.Diagram.productDiagram F ⋙ T

def targetDiagram : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ BigCrystallineSite.Object p B J δ fY :=
  G ⋙ BoundedFrame.Diagram.productDiagram ((G).obj F)

def comparison : sourceDiagram g hg n F ⟶ targetDiagram g hg n F where
  app U := (QY).map (prodComparison G F U)
  naturality U V α := by
    change (QY).map ((G).map (prod.map (𝟙 F) α)) ≫ (QY).map (prodComparison G F V) =
      (QY).map (prodComparison G F U) ≫ (QY).map (prod.map (𝟙 ((G).obj F)) ((G).map α))
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (QY).map
    exact (prodComparison_natural G (𝟙 F) α).trans
      (congrArg (fun t : (G).obj F ⟶ (G).obj F => prodComparison G F U ≫ prod.map t ((G).map α))
        ((G).map_id F))

def sourceProjection : sourceDiagram g hg n F ⟶ G ⋙ QY :=
  Functor.whiskerRight (BoundedFrame.Diagram.projection F) T

def targetProjection : targetDiagram g hg n F ⟶ G ⋙ QY :=
  Functor.whiskerLeft G (BoundedFrame.Diagram.projection ((G).obj F))

theorem projection : comparison g hg n F ≫ targetProjection g hg n F = sourceProjection g hg n F := by
  apply NatTrans.ext
  funext U
  change (QY).map (prodComparison G F U) ≫
      (BoundedFrame.Diagram.projection ((G).obj F)).app ((G).obj U) =
    (T).map ((BoundedFrame.Diagram.projection F).app U)
  rw [BoundedFrame.Diagram.projection_app, BoundedFrame.Diagram.projection_app]
  change (QY).map (prodComparison G F U) ≫ (QY).map prod.snd = (QY).map ((G).map prod.snd)
  rw [← Functor.map_comp, prodComparison_snd]

def sourceFrameProjection : sourceDiagram g hg n F ⟶ (Functor.const _).obj ((G).obj F).obj :=
  Functor.whiskerRight (BoundedFrame.Symbols.frameProjection F) T

def targetFrameProjection : targetDiagram g hg n F ⟶ (Functor.const _).obj ((G).obj F).obj :=
  Functor.whiskerLeft G (BoundedFrame.Symbols.frameProjection ((G).obj F))

theorem frameProjection : comparison g hg n F ≫ targetFrameProjection g hg n F =
    sourceFrameProjection g hg n F := by
  apply NatTrans.ext
  funext U
  change (QY).map (prodComparison G F U) ≫
      (BoundedFrame.Symbols.frameProjection ((G).obj F)).app ((G).obj U) =
    (T).map ((BoundedFrame.Symbols.frameProjection F).app U)
  rw [BoundedFrame.Symbols.frameProjection_app, BoundedFrame.Symbols.frameProjection_app]
  change (QY).map (prodComparison G F U) ≫ (QY).map prod.fst = (QY).map ((G).map prod.fst)
  rw [← Functor.map_comp, prodComparison_fst]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.GeneralFrameComparison
