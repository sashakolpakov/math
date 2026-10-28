import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCounit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates

/-! # PD Intrinsic Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicCoordinates.Intrinsic

noncomputable section

/-! Original Cohomology forms on the small-site version of an IntegralComparison frame
identify naturally with that frame's original IntegralComparison de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

def presentationIso := Functor.isoWhiskerLeft GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62.op
  (PDComplexCoordinates.iso p k X)

def roundTripIso :=
  Functor.isoWhiskerRight (NatIso.op (GeometricComparison.SmallCrystallineCounit.SmallCrystallineAdapter.counit (p := p) (k := k) (X := X)).symm)
    (BigCrystallineSite.fromSmall.op ⋙
      GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor (Witt.Crystalline.wittStructureMap p k X))

def iso : GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62.op ⋙
      PDComplexCoordinates.originalFunctor p k X ≅
    BigCrystallineSite.fromSmall.op ⋙
      GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor (Witt.Crystalline.wittStructureMap p k X) :=
  presentationIso p k X ≪≫ roundTripIso p k X

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicCoordinates.Intrinsic
