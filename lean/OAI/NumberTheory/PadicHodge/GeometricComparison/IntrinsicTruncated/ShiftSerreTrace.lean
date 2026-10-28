import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTopEdgeBase
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.SmallTrace
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Connected
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleCoverTraceBase

/-! # Shift Serre Trace -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftSerreTrace.AbelianModel

noncomputable section

section

/-! The original finite étale shifted source carries the actual
finite-coefficient Serre trace on its native common affine cover. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m) (hpos : 0 < A.dimension)
local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n
local notation "X" => A.truncatedShiftModel n m hm
local notation "Y" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.scheme (A.truncatedModel n)
local notation "f" => A.truncatedShiftOver n m hm
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase.sourceCover q (ZMod q) n (f)

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftOver_finite : IsFinite (A.truncatedShiftOver n m hm).left :=
  A.truncatedShiftMap_finite n m hm

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftOver_etale : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left :=
  A.truncatedShiftMap_etale n m hm

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonCover_top : (⨆ i, V i) = ⊤ :=
  IntegralComparison.TruncatedModel.MorphismCover.cover q (ZMod q) n (f)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonCover_affine (i : IntegralComparison.TruncatedModel.MorphismCover.Index q (ZMod q) n (f)) :
    IsAffineOpen (V i) :=
  (IntegralComparison.TruncatedModel.MorphismCover.opens q (ZMod q) n (f) i).property

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonTraceEquiv : A.TruncatedShiftCommonTopForms n m hm ≃+
    IntegralComparison.Projective.TopTracePairing.coefficientRing R :=
  IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.traceIso Y X f (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension V
    (A.truncatedShiftCommonCover_top n m hm) (A.truncatedShiftCommonCover_affine n m hm) hpos
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)

attribute [local irreducible] IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.traceIso IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.trace

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonTraceEquiv_apply (x : A.TruncatedShiftCommonTopForms n m hm) :
    A.truncatedShiftCommonTraceEquiv n m hm hpos x =
      IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.trace Y X f (A.truncatedTraceMorphism n)
        (A.truncatedTraceDimension n + 2) le_rfl A.dimension V
        (A.truncatedShiftCommonCover_top n m hm) (A.truncatedShiftCommonCover_affine n m hm) hpos x := by
  dsimp only [Geometry.AbelianH1Model.truncatedShiftCommonTraceEquiv]
  exact IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.traceIso_apply Y X f (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension V
    (A.truncatedShiftCommonCover_top n m hm) (A.truncatedShiftCommonCover_affine n m hm) hpos
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm) x

end

/-! The trace on the original common source cover is the genuine
finite-coefficient Serre trace, with its canonical cover coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m) (hpos : 0 < A.dimension)
local notation "X" => A.truncatedShiftModel n m hm
local notation "Y" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.scheme (A.truncatedModel n)
local notation "f" => A.truncatedShiftOver n m hm
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase.sourceCover q (ZMod q) n (f)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonSerreIso :
    AddCommGrpCat.of (A.TruncatedShiftCommonTopForms n m hm) ≅
      IntegralComparison.FiniteEtale.ProperTraceBase.cohomology Y X f (A.truncatedTraceMorphism n) A.dimension :=
  IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.serreIso Y X f (A.truncatedTraceMorphism n)
    A.dimension V (A.truncatedShiftCommonCover_top n m hm)
    (A.truncatedShiftCommonCover_affine n m hm) hpos

attribute [local irreducible] IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.trace
  IntegralComparison.FiniteEtale.ProperTraceBase.trace IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.serreIso

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftCommonTraceEquiv_serre (x : A.TruncatedShiftCommonTopForms n m hm) :
    A.truncatedShiftCommonTraceEquiv n m hm hpos x =
      IntegralComparison.FiniteEtale.ProperTraceBase.trace Y X f (A.truncatedTraceMorphism n)
        (A.truncatedTraceDimension n + 2) le_rfl A.dimension
        ((A.truncatedShiftCommonSerreIso n m hm hpos).hom x) := by
  rw [A.truncatedShiftCommonTraceEquiv_apply]
  dsimp only [Geometry.AbelianH1Model.truncatedShiftCommonSerreIso]
  exact IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite.trace_serre Y X f (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension V
    (A.truncatedShiftCommonCover_top n m hm) (A.truncatedShiftCommonCover_affine n m hm) hpos x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftSerreTrace.AbelianModel
