import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleCoverTraceBase

/-! # Finite Etale Trace Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleTraceRefinement

noncomputable section

/-! The genuine source Serre trace commutes with actual refinements
of its affine Čech cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
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
  {κ τ : Type u} (V : κ → Y.left.Opens) (W : τ → Y.left.Opens)
  (r : FormalCoproduct.mk τ W ⟶ FormalCoproduct.mk κ V)
  (hV : ⨆ j, V j = ⊤) (hW : ⨆ j, W j = ⊤)
  (haV : ∀ j, IsAffineOpen (V j)) (haW : ∀ j, IsAffineOpen (W j)) (hg : 0 < g)
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local notation "V₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R Y X f (OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace.cover X i)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local instance source_qc : (M).IsQuasicoherent := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
attribute [local irreducible] EtaleProperTraceBase.IntrinsicFinite.trace

omit [IsArtinianRing R] [IsLocalRing R] [Smooth X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g Y.hom] in
theorem trace (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g) :
    EtaleCoverTraceBase.IntrinsicFinite.trace X Y f i B hB g W hW haW hg
        (HomologicalComplex.homologyMap (ModuleCech.CoverRefinement.map R Y V W r M) g x) =
      EtaleCoverTraceBase.IntrinsicFinite.trace X Y f i B hB g V hV haV hg x := by
  have he := ModuleCech.TraceRefinement.map_eq_positiveCoverIso R Y V W r hV hW haV haW M g hg
  have ht := ModuleCech.PositiveTransitivity.hom_comp R Y V W V₀ hV hW
    (RefinedTransferTrace.inverseCover_top R Y X f (TopFormTrace.cover X i)
      (TopFormTrace.cover_top X i)) haV haW
    (RefinedTransferTrace.inverseCover_affine R Y X f (TopFormTrace.cover X i)
      (TopFormTrace.cover_affine X i)) M g hg
  have hs : (G).map (HomologicalComplex.homologyMap (ModuleCech.CoverRefinement.map R Y V W r M) g) ≫
      (EtaleCoverTraceBase.IntrinsicFinite.coverIso X Y f i g W hW haW hg).hom =
    (EtaleCoverTraceBase.IntrinsicFinite.coverIso X Y f i g V hV haV hg).hom := by
    rw [he]
    exact ht
  change EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g
      ((EtaleCoverTraceBase.IntrinsicFinite.coverIso X Y f i g W hW haW hg).hom
        (HomologicalComplex.homologyMap (ModuleCech.CoverRefinement.map R Y V W r M) g x)) =
    EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g
      ((EtaleCoverTraceBase.IntrinsicFinite.coverIso X Y f i g V hV haV hg).hom x)
  exact congrArg (EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g)
    (ConcreteCategory.congr_hom hs x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleTraceRefinement
