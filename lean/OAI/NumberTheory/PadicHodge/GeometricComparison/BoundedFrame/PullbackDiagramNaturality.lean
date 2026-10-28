import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ProductPullbackNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change

/-! # Pullback Diagram Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagramNaturality.BoundedFramePullbackDiagramNaturality

noncomputable section

/-! The arbitrary geometric product comparison commutes with compatible
changes of the original source and target crystalline frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {FX FX' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY FY' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : FX ⟶ FX') (b : FY ⟶ FY')
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)
  (α' : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX' ⟶ FY')

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n

theorem natural (h : (G).map a ≫ α' = α ≫ b) :
    Functor.whiskerRight (IntegralComparison.BoundedFrame.Change.diagramMap a) T ≫
      PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX' FY' α' =
    PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX FY α ≫
      Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Change.diagramMap b) := by
  apply NatTrans.ext
  funext U
  change (QY).map ((G).map (prod.map a (𝟙 U))) ≫
      (QY).map (prod.lift ((G).map prod.fst ≫ α') ((G).map prod.snd)) =
    (QY).map (prod.lift ((G).map prod.fst ≫ α) ((G).map prod.snd)) ≫
      (QY).map (prod.map b (𝟙 ((G).obj U)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (QY).map (Frame.ProductPullbackNaturality.FrameProductPullbackNaturality.square G a b α α' h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagramNaturality.BoundedFramePullbackDiagramNaturality
