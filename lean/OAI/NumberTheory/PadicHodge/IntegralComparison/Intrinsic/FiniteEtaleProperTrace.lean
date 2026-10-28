import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleProperTraceBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTrace

/-! # Finite Etale Proper Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleProperTrace

noncomputable section

/-! Native proper trace commutes with actual finite étale top-form transfer. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
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
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace.cover X i
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R Y X f (U)

variable [SmoothOfRelativeDimension g Y.hom] [Smooth Y.hom] [IsProper Y.hom]

omit [SmoothOfRelativeDimension g Y.hom] [Smooth Y.hom] [IsProper Y.hom] in
omit [IsArtinianRing R] [IsLocalRing R] [GeometricallyConnected X.hom] in
theorem trace_transfer (x : EtaleProperTraceBase.IntrinsicFinite.cohomology X Y f i g) :
    TopFormTrace.trace X i B hB g (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U g x) =
      EtaleProperTraceBase.IntrinsicFinite.trace X Y f i B hB g x := by
  have h := congrArg (fun z => z ≫ IntegralComparison.Smooth.ProjectiveFormTrace.trace X i B hB g)
    (EtaleProperTraceBase.IntrinsicFinite.transfer_square X Y f i g)
  simp only [Category.assoc] at h
  rw [FiniteEtale.ProperTrace.trace_transfer] at h
  have hx := ConcreteCategory.congr_hom h x
  change TopFormTrace.trace X i B hB g
    (HomologicalComplex.homologyMap (ModuleCechTrace.trace R Y X f U g) g x) = _ at hx
  rw [ModuleTraceHomology.top_trace] at hx
  exact hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleProperTrace
