import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameGenerators

/-! # Postcomposition Generators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PostcompositionGenerators.FramePostcompositionGenerators

noncomputable section

/-! Ring formulas for frame maps survive geometric postcomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (jY : Y ⟶ Z) (jX : X ⟶ Z)
  (hg : g ≫ fY = fX) (hjY : jY ≫ fZ = fY) (hjX : jX ≫ fZ = fX)
  (h : g ≫ jY = jX) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj FX ⟶ FY)
  {A D : Type v} (qX : A → FX.obj.ring) (qY : D → FY.obj.ring) (r : D → A)

theorem map (hα : ∀ a, α.hom.ringMap (qY a) = qX (r a)) (a : D) :
    (Crystalline.FramePostcomposition.CrystallineFramePostcomposition.map g jY jX hg hjY hjX h n α).hom.ringMap
      (Smooth.WittFrameGenerators.SmoothWittFrameGenerators.postcompose jY hjY n FY qY a) =
    Smooth.WittFrameGenerators.SmoothWittFrameGenerators.postcompose jX hjX n FX qX (r a) := by
  rw [Crystalline.FramePostcomposition.CrystallineFramePostcomposition.ringMap]
  exact hα a

theorem map_of_ringMap
    (β : (IntegralComparison.BoundedOpen.Equivalence.postcompose jX hjX n).obj FX ⟶
      (IntegralComparison.BoundedOpen.Equivalence.postcompose jY hjY n).obj FY)
    (heq : β.hom.ringMap = α.hom.ringMap)
    (hα : ∀ a, α.hom.ringMap (qY a) = qX (r a)) (a : D) :
    β.hom.ringMap (Smooth.WittFrameGenerators.SmoothWittFrameGenerators.postcompose jY hjY n FY qY a) =
      Smooth.WittFrameGenerators.SmoothWittFrameGenerators.postcompose jX hjX n FX qX (r a) := by
  rw [heq]
  exact hα a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PostcompositionGenerators.FramePostcompositionGenerators
