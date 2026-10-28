import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifts
import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow

/-! # Intrinsic Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts

noncomputable section

/-! # Comparing the original big-site and native crystalline coordinate lifts -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "base" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

def inclusion : Site.Object p k X ⥤ FrameLifts.BigCrystallineFrameLifts.Site p W B I γ base :=
  NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to65 ⋙ NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.fromSmall

theorem residualMap (Q : Site.Object p k X) :
    FrameLifts.BigCrystallineFrameLifts.residualMap p W B I γ base ((inclusion p k B).obj Q) =
      (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q).symm.toRingHom.comp (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q).toRingHom := by
  have he : CommRingCat.ofHom
      (FrameLifts.BigCrystallineFrameLifts.residualMap p W B I γ base ((inclusion p k B).obj Q)) =
      CommRingCat.ofHom ((NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q).symm.toRingHom.comp
        (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q).toRingHom) := by
    apply Spec.map_injective
    rw [FrameLifts.BigCrystallineFrameLifts.residualMap_spec]
    change (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueSchemeIso Q).hom ≫ Q.immersion =
      Spec.map (CommRingCat.ofHom ((NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q).symm.toRingHom.comp
        (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q).toRingHom))
    rw [CommRingCat.ofHom_comp, Spec.map_comp, AffineFrameCover.CrystallineAffineFrameCover.residualMap_spec]
    rfl
  exact congrArg CommRingCat.Hom.hom he

def lift (Q : Site.Object p k X) (i : σ) : Q.thickening.ring :=
  FrameLifts.BigCrystallineFrameLifts.lift p W B σ I γ base a ((inclusion p k B).obj Q) i

theorem reduction_lift (Q : Site.Object p k X) (i : σ) :
    Q.thickening.reduction (lift p k B σ a Q i) = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i) := by
  have h := FrameLifts.BigCrystallineFrameLifts.reduction_lift p W B σ I γ base a ((inclusion p k B).obj Q) i
  rw [residualMap] at h
  have hh := congrArg (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q) h
  change (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q) (Ideal.Quotient.mk (RingHom.ker Q.thickening.reduction)
    (lift p k B σ a Q i)) = (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q) ((NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv Q).symm
      (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i))) at hh
  rw [RingEquiv.apply_symm_apply] at hh
  exact hh

def difference (Q : Site.Object p k X) (i : σ) : Q.thickening.ring :=
  CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i - lift p k B σ a Q i

theorem difference_mem (Q : Site.Object p k X) (i : σ) :
    difference p k B σ a Q i ∈ RingHom.ker Q.thickening.reduction := by
  change Q.thickening.reduction (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i - lift p k B σ a Q i) = 0
  rw [map_sub, CrystallineFrame.Lifts.CrystallineFrameLifts.reduction_lift, reduction_lift, sub_self]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts
