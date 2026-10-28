import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftSerreTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.IntrinsicTraceBijective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleCoverTrace

/-! # Shift Trace -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTrace.AbelianModel

noncomputable section

/-! The actual finite-level shifted source has a normalized additive
top-form trace on the original common cover. Pullback multiplies its
trace by the original special-fiber finite-flat rank. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m) (hpos : 0 < A.dimension)
local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n
local notation "X" => A.truncatedShiftModel n m hm
local notation "Y" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.scheme (A.truncatedModel n)
local notation "f" => A.truncatedShiftOver n m hm
local notation "U" => A.truncatedSmallCover n
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase.sourceCover q (ZMod q) n (f)

include hpos in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftTopTransfer_bijective :
    Function.Bijective (IntegralComparison.IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U A.dimension) :=
  IntegralComparison.FiniteEtale.IntrinsicTraceBijective.Intrinsic.bijective Y X f (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    U (A.truncatedSmallCover_top n) (A.truncatedSmallCover_affine n) hpos

attribute [local irreducible] IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.trace
  IntegralComparison.IntrinsicDeRham.TopEdgeMap.Intrinsic.rowMap

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonTrace_pullback (y : A.specialFiber.scheme.left)
    (x : A.TruncatedSmallTopForms n) :
    A.truncatedShiftCommonTraceEquiv n m hm hpos (A.truncatedShiftCommonPullback n m hm x) =
      (A.truncatedShiftSpecial m).finrank y • A.truncatedSmallTopFormTrace n hpos x := by
  let V₂ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R Y
  let pairs := IntegralComparison.TruncatedModel.MorphismCover.pairs q (ZMod q) n (f)
  let r := IntegralComparison.TruncatedModel.MorphismRefinement.target q (ZMod q) n (f)
  have h := IntegralComparison.Intrinsic.FiniteEtaleCoverTrace.pullback_trace Y X f (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension U V
    (A.truncatedSmallCover_top n) (A.truncatedShiftCommonCover_top n m hm)
    (A.truncatedSmallCover_affine n) (A.truncatedShiftCommonCover_affine n m hm) hpos
    (IntegralComparison.Affine.MorphismIntrinsicCechTotal.Intrinsic.openRefinement R f pairs V₂ r).f
    (IntegralComparison.Affine.MorphismIntrinsicCechTotal.Intrinsic.coverLE R f pairs V₂ r) (A.truncatedReduction n y) x
  have ht : IntegralComparison.Intrinsic.TopFormTrace.trace Y (A.truncatedTraceMorphism n)
      (A.truncatedTraceDimension n + 2) le_rfl A.dimension
      ((IntegralComparison.Intrinsic.FiniteEtaleCoverTrace.targetCoverIso Y (A.truncatedTraceMorphism n)
        A.dimension U (A.truncatedSmallCover_top n) (A.truncatedSmallCover_affine n) hpos).hom x) =
      A.truncatedSmallTopFormTrace n hpos x := by
    rw [← A.truncatedTopFormTrace_eq]
    rfl
  rw [ht] at h
  change IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.trace Y X f (A.truncatedTraceMorphism n)
      (A.truncatedTraceDimension n + 2) le_rfl A.dimension V
      (A.truncatedShiftCommonCover_top n m hm) (A.truncatedShiftCommonCover_affine n m hm) hpos
      (A.truncatedShiftCommonPullback n m hm x) =
    (A.truncatedShiftMap n m hm).finrank (A.truncatedReduction n y) •
      A.truncatedSmallTopFormTrace n hpos x at h
  rw [A.truncatedShiftMap_finrank n m hm] at h
  rw [A.truncatedShiftCommonTraceEquiv_apply]
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTrace.AbelianModel
