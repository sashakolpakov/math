import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDCoordinates

/-! # Crystalline PD Component -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDComponent

noncomputable section

/-! The coordinate comparison on an open crystalline diagram is the
literal small-frame coordinate map at each object. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {C : Type v} [Category.{z} C]
  (F : C ⥤ BigCrystallineSite.Object p (WittVector p k)
    (Ideal.span {(p : WittVector p k)}) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k X))
  (hOpen : ∀ c, IsOpenImmersion (F.obj c).mapToX)

theorem hom_app (c : C) : (CrystallinePDCoordinates.iso p k X F hOpen).hom.app (op c) =
    (Small.PDIntrinsicCoordinates.Intrinsic.iso p k X).hom.app (op (CrystallineDiagram.object F hOpen c)) := by
  change (Small.PDIntrinsicCoordinates.Intrinsic.iso p k X).hom.app _ ≫
    (GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor (Witt.Crystalline.wittStructureMap p k X)).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id
    ((Small.PDIntrinsicCoordinates.Intrinsic.iso p k X).hom.app
      (op (CrystallineDiagram.object F hOpen c)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDComponent
