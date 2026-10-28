import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallineDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicCoordinates

/-! # Crystalline PD Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDCoordinates

noncomputable section

/-! The canonical small-site presentation of an open crystalline
diagram preserves its actual de Rham complex, naturally in the diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {C : Type v} [Category.{w} C]
  (F : C ⥤ BigCrystallineSite.Object p (WittVector p k)
    (Ideal.span {(p : WittVector p k)}) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k X))
  (hOpen : ∀ c, IsOpenImmersion (F.obj c).mapToX)

def sourceIso := Functor.isoWhiskerLeft (CrystallineDiagram.functor F hOpen).op
  (Small.PDIntrinsicCoordinates.Intrinsic.iso p k X)

def targetIso := Functor.isoWhiskerRight (NatIso.op (CrystallineDiagram.inclusionIso F hOpen).symm)
  (GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor (Witt.Crystalline.wittStructureMap p k X))

def iso : (CrystallineDiagram.functor F hOpen ⋙ GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62).op ⋙
      Small.PDComplexCoordinates.originalFunctor p k X ≅
    F.op ⋙ GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor (Witt.Crystalline.wittStructureMap p k X) :=
  sourceIso p k X F hOpen ≪≫ targetIso p k X F hOpen

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDCoordinates
