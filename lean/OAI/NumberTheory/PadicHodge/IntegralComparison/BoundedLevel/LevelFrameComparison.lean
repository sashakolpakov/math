import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Products
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols

/-! # Level Frame Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison

noncomputable section

/-!
# IntegralComparison: native bounded frame product diagrams are compatible with inclusions between Witt levels
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  [Fact p.Prime] [IsSeparated f]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m

def sourceDiagram : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ BigCrystallineSite.Object p B J δ f :=
  BoundedFrame.Diagram.productDiagram F

def targetDiagram : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ BigCrystallineSite.Object p B J δ f :=
  G ⋙ BoundedFrame.Diagram.productDiagram ((G).obj F)

def comparison : sourceDiagram f n F ⟶ targetDiagram f n m hnm F where
  app U := (QY).map (prodComparison G F U)
  naturality U V α := by
    change (QY).map ((G).map (prod.map (𝟙 F) α)) ≫ (QY).map (prodComparison G F V) =
      (QY).map (prodComparison G F U) ≫ (QY).map (prod.map (𝟙 ((G).obj F)) ((G).map α))
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (QY).map
    exact (prodComparison_natural G (𝟙 F) α).trans
      (congrArg (fun t : (G).obj F ⟶ (G).obj F => prodComparison G F U ≫ prod.map t ((G).map α))
        ((G).map_id F))

instance comparison_app_isIso (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) :
    IsIso ((comparison f n m hnm F).app U) := by
  change IsIso ((QY).map (prodComparison G F U))
  infer_instance

instance comparison_isIso : IsIso (comparison f n m hnm F) := NatIso.isIso_of_isIso_app _

def sourceProjection : sourceDiagram f n F ⟶ G ⋙ QY :=
  BoundedFrame.Diagram.projection F

def targetProjection : targetDiagram f n m hnm F ⟶ G ⋙ QY :=
  Functor.whiskerLeft G (BoundedFrame.Diagram.projection ((G).obj F))

theorem projection : comparison f n m hnm F ≫ targetProjection f n m hnm F = sourceProjection f n m hnm F := by
  apply NatTrans.ext
  funext U
  change (QY).map (prodComparison G F U) ≫
      (BoundedFrame.Diagram.projection ((G).obj F)).app ((G).obj U) =
    (BoundedFrame.Diagram.projection F).app U
  rw [BoundedFrame.Diagram.projection_app, BoundedFrame.Diagram.projection_app]
  change (QY).map (prodComparison G F U) ≫ (QY).map prod.snd = (QY).map ((G).map prod.snd)
  rw [← Functor.map_comp, prodComparison_snd]

def sourceFrameProjection : sourceDiagram f n F ⟶ (Functor.const _).obj ((G).obj F).obj :=
  BoundedFrame.Symbols.frameProjection F

def targetFrameProjection : targetDiagram f n m hnm F ⟶ (Functor.const _).obj ((G).obj F).obj :=
  Functor.whiskerLeft G (BoundedFrame.Symbols.frameProjection ((G).obj F))

theorem frameProjection : comparison f n m hnm F ≫ targetFrameProjection f n m hnm F =
    sourceFrameProjection f n m hnm F := by
  apply NatTrans.ext
  funext U
  change (QY).map (prodComparison G F U) ≫
      (BoundedFrame.Symbols.frameProjection ((G).obj F)).app ((G).obj U) =
    (BoundedFrame.Symbols.frameProjection F).app U
  rw [BoundedFrame.Symbols.frameProjection_app, BoundedFrame.Symbols.frameProjection_app]
  change (QY).map (prodComparison G F U) ≫ (QY).map prod.fst = (QY).map ((G).map prod.fst)
  rw [← Functor.map_comp, prodComparison_fst]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison
