import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison

/-! # Level Diagram Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelDiagramNaturality.BoundedLevelDiagramNaturality

noncomputable section

/-! The canonical bounded-level product comparison is natural in the frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "Qm" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m

theorem natural {F F' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : F ⟶ F') :
    IntegralComparison.BoundedFrame.Change.diagramMap α ≫ IntegralComparison.BoundedLevel.LevelFrameComparison.comparison f n m hnm F' =
      IntegralComparison.BoundedLevel.LevelFrameComparison.comparison f n m hnm F ≫
        Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Change.diagramMap ((G).map α)) := by
  apply NatTrans.ext
  funext U
  change (Qm).map ((G).map (prod.map α (𝟙 U))) ≫ (Qm).map (prodComparison G F' U) =
    (Qm).map (prodComparison G F U) ≫ (Qm).map (prod.map ((G).map α) (𝟙 ((G).obj U)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (Qm).map
  exact (prodComparison_natural G α (𝟙 U)).trans
    (congrArg (fun t => prodComparison G F U ≫ prod.map ((G).map α) t) ((G).map_id U))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelDiagramNaturality.BoundedLevelDiagramNaturality
