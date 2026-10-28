import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleProperTraceBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceCoverNaturality

/-! # Etale Cover Trace Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite

noncomputable section

/-! The genuine finite-coefficient Serre trace transported to any
affine cover of the finite étale source. Only the target is embedded. -/
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
  [SmoothOfRelativeDimension g Y.hom] [Smooth Y.hom] [IsProper Y.hom] [Y.left.IsSeparated]
  {κ : Type u} (V : κ → Y.left.Opens)
  (hV : ⨆ j, V j = ⊤) (haV : ∀ j, IsAffineOpen (V j)) (hg : 0 < g)
local notation "U₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace.cover X i
local notation "V₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R Y X f (U₀)
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local instance source_qc : (M).IsQuasicoherent := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g

def coverIso : AddCommGrpCat.of (IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g) ≅
    AddCommGrpCat.of (EtaleProperTraceBase.IntrinsicFinite.cohomology X Y f i g) :=
  ModuleCech.PositiveCover.Comparison.iso R Y V V₀ hV
    (RefinedTransferTrace.inverseCover_top R Y X f U₀ (TopFormTrace.cover_top X i))
    haV (RefinedTransferTrace.inverseCover_affine R Y X f U₀
      (TopFormTrace.cover_affine X i)) M g hg

def trace : IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g →+ Projective.TopTracePairing.coefficientRing R :=
  (EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g).comp (coverIso X Y f i g V hV haV hg).hom.hom

def serreIso : AddCommGrpCat.of (IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g) ≅
    FiniteEtale.ProperTraceBase.cohomology X Y f i g :=
  coverIso X Y f i g V hV haV hg ≪≫ EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g

omit [IsArtinianRing R] [IsLocalRing R] [Smooth X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g Y.hom] in
theorem trace_serre (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g) :
    trace X Y f i B hB g V hV haV hg x =
      FiniteEtale.ProperTraceBase.trace X Y f i B hB g
        ((serreIso X Y f i g V hV haV hg).hom x) := rfl

variable [GeometricallyConnected Y.hom]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)

def traceIso : IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g ≃+ Projective.TopTracePairing.coefficientRing R :=
  (coverIso X Y f i g V hV haV hg).addCommGroupIsoToAddEquiv.trans
    (EtaleProperTraceBase.IntrinsicFinite.traceIso X Y f i B hB g s hs)

omit [Smooth X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g Y.hom] in
theorem traceIso_apply (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g) :
    traceIso X Y f i B hB g V hV haV hg s hs x = trace X Y f i B hB g V hV haV hg x := by
  exact EtaleProperTraceBase.IntrinsicFinite.traceIso_apply X Y f i B hB g s hs _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleCoverTraceBase.IntrinsicFinite
