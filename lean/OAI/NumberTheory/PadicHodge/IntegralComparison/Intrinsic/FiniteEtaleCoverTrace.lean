import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleCoverTraceBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleProperTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleTraceRefinement

/-! # Finite Etale Cover Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleCoverTrace

noncomputable section

/-! The transfer-defined source trace is the genuine Serre trace
transported from the target projective cover. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [SmoothOfRelativeDimension g Y.hom] [Smooth Y.hom] [IsProper Y.hom]
  [X.left.IsSeparated] [Y.left.IsSeparated]
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (hU : ⨆ j, U j = ⊤) (hV : ⨆ j, V j = ⊤)
  (haU : ∀ j, IsAffineOpen (U j)) (haV : ∀ j, IsAffineOpen (V j)) (hg : 0 < g)
local notation "U₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace.cover X i
local notation "V₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R Y X f (U₀)
local notation "W" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R Y X f U
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local instance comparison_source_qc : (M).IsQuasicoherent := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
local instance comparison_target_qc : (N).IsQuasicoherent := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g

def targetCoverIso := ModuleCech.PositiveCover.Comparison.iso R X U U₀ hU
  (TopFormTrace.cover_top X i) haU (TopFormTrace.cover_affine X i) N g hg

omit [IsArtinianRing R] [IsLocalRing R] [GeometricallyConnected X.hom] in
theorem transfer (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y W g) :
    TopFormTrace.trace X i B hB g
        ((targetCoverIso X i g U hU haU hg).hom (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U g x)) =
      EtaleCoverTraceBase.IntrinsicFinite.trace X Y f i B hB g W
        (RefinedTransferTrace.inverseCover_top R Y X f U hU)
        (RefinedTransferTrace.inverseCover_affine R Y X f U haU) hg x := by
  have h := ModuleTraceCoverNaturality.trace R Y X f U U₀ g hU
    (TopFormTrace.cover_top X i) haU (TopFormTrace.cover_affine X i) hg x
  exact (congrArg (TopFormTrace.trace X i B hB g) h).trans
    (FiniteEtaleProperTrace.trace_transfer X Y f i B hB g _)

omit [IsArtinianRing R] [IsLocalRing R] [GeometricallyConnected X.hom] in
theorem pullback_trace [PreconnectedSpace X.left]
    (r : κ → ι) (hr : ∀ j, V j ≤ f.left ⁻¹ᵁ U (r j))
    (y : X.left) (x : IntrinsicDeRham.TopEdge.Intrinsic.source R X U g) :
    EtaleCoverTraceBase.IntrinsicFinite.trace X Y f i B hB g V hV haV hg
        (IntrinsicDeRham.TopEdgeMap.Intrinsic.rowMap R Y X V U g
          (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.sheafMap R f U V r hr) x) =
      f.left.finrank y • TopFormTrace.trace X i B hB g
        ((targetCoverIso X i g U hU haU hg).hom x) := by
  rw [TopFormPullbackRefinement.pullback]
  have h := FiniteEtaleTraceRefinement.trace X Y f i B hB g W V
    (TopFormPullbackRefinement.refinement R Y X f U V r hr)
    (RefinedTransferTrace.inverseCover_top R Y X f U hU) hV
    (RefinedTransferTrace.inverseCover_affine R Y X f U haU) haV hg
    (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.pullback R Y X f U g x)
  apply h.trans
  rw [← transfer X Y f i B hB g U hU haU hg]
  rw [TopFormTransferDegree.pullback_trace R Y X f U g y x,
    map_nsmul, map_nsmul]

variable (t : IntrinsicDeRham.TopEdge.Intrinsic.source R X U g ≃+ Projective.TopTracePairing.coefficientRing R)
  (hb : Function.Bijective (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U g))
  (ht : ∀ z, t z = TopFormTrace.trace X i B hB g
    ((targetCoverIso X i g U hU haU hg).hom z))

attribute [local irreducible] EtaleProperTraceBase.IntrinsicFinite.trace

include ht in
omit [IsArtinianRing R] [IsLocalRing R] [GeometricallyConnected X.hom] in
theorem refined_eq (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g) :
    RefinedTransferTrace.trace R Y X f U V hU hV haU haV g hg t hb x =
      EtaleCoverTraceBase.IntrinsicFinite.trace X Y f i B hB g V hV haV hg x := by
  let e := RefinedTransferTrace.coverIso R Y X f U V hU hV haU haV g hg
  change t (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U g (e.inv x)) = _
  rw [ht]
  have h := transfer X Y f i B hB g U hU haU hg (e.inv x)
  apply h.trans
  change EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g
      ((EtaleCoverTraceBase.IntrinsicFinite.coverIso X Y f i g W
        (RefinedTransferTrace.inverseCover_top R Y X f U hU)
        (RefinedTransferTrace.inverseCover_affine R Y X f U haU) hg).hom (e.inv x)) =
    EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g ((EtaleCoverTraceBase.IntrinsicFinite.coverIso X Y f i g V hV haV hg).hom x)
  apply congrArg (EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g)
  exact ConcreteCategory.congr_hom
    (ModuleCech.PositiveTransitivity.inv_hom R Y W V V₀
      (RefinedTransferTrace.inverseCover_top R Y X f U hU) hV
      (RefinedTransferTrace.inverseCover_top R Y X f U₀ (TopFormTrace.cover_top X i))
      (RefinedTransferTrace.inverseCover_affine R Y X f U haU) haV
      (RefinedTransferTrace.inverseCover_affine R Y X f U₀ (TopFormTrace.cover_affine X i))
      M g hg) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleCoverTrace
