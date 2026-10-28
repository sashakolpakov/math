import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDPointSymbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FrameSymbols

/-! # PD Intrinsic Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicSymbols.Intrinsic

noncomputable section

/-! The original small-site to native-frame coordinates preserve each
literal divided-power differential symbol. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

variable (U : Witt.Crystalline.CrystallineObject p k X)

local instance nativeAlgebra : Algebra (WittVector p k) U.ring := U.base.toAlgebra

local instance roundTripAlgebra : Algebra (WittVector p k)
    (BigCrystallineSite.fromSmall.obj
      (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to65Object (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U))).ring :=
  (BigCrystallineSite.fromSmall.obj
    (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to65Object (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U))).base.toAlgebra

theorem hom_symbol (n : ℕ) (a : U.ring) (v : Fin n → U.ring) :
    ((PDIntrinsicCoordinates.Intrinsic.iso p k X).hom.app (op U)).f n
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol (WittVector p k)
          (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U).thickening.ring
          (RingHom.ker (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U).thickening.reduction)
          (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U).thickening.dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol (WittVector p k) U.ring U.ideal U.dividedPowers a v := by
  change (((PDIntrinsicCoordinates.Intrinsic.roundTripIso p k X).hom.app (op U)).f n)
    (((PDComplexCoordinates.pointIso p k X
      (op (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U))).hom.f n)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ a v)) = _
  erw [PDPointSymbols.hom_symbol p k X
    (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U) n a v]
  change (((GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor
    (Witt.Crystalline.wittStructureMap p k X)).map
      (BigCrystallineSite.fromSmall.map (GeometricComparison.SmallCrystallineCounit.SmallCrystallineAdapter.counitAt U).inv).op).f n)
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol _ _ _ _ a v) = _
  erw [Crystalline.FrameSymbols.map_symbol (Witt.Crystalline.wittStructureMap p k X)
    (BigCrystallineSite.fromSmall.map (GeometricComparison.SmallCrystallineCounit.SmallCrystallineAdapter.counitAt U).inv) n a v]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicSymbols.Intrinsic
