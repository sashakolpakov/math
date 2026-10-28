import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTraceBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceHomology

/-! # Etale Proper Trace Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite

noncomputable section

/-! The proper finite étale source trace on the actual inverse-image
Čech cover uses only the target projective embedding. -/
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
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "T" => CategoryTheory.Functor.obj (Scheme.Modules.pushforward f.left) (M)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R

abbrev cohomology := IntrinsicDeRham.TopEdge.Intrinsic.source R Y V g

def serreIso : AddCommGrpCat.of (cohomology X Y f i g) ≅
    FiniteEtale.ProperTraceBase.cohomology X Y f i g :=
  ModuleTraceHomology.pushforwardIso R Y X f U g g ≪≫
    ModuleCech.Pushforward.Comparison.cohomologyIso R X (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) i T
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R)) g

def trace : cohomology X Y f i g →+ Projective.TopTracePairing.coefficientRing R :=
  ((serreIso X Y f i g).hom ≫ FiniteEtale.ProperTraceBase.trace X Y f i B hB g).hom

omit [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsClosedImmersion (Over.Hom.left i)] [GeometricallyConnected X.hom] in
theorem transfer_square :
    (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R Y X f U g) g) ≫
      (TopFormTrace.serreIso X i g).hom =
    (serreIso X Y f i g).hom ≫
      (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
        (FiniteEtale.AdjunctionTrace.trace X Y f i g) := by
  have h₁ := ModuleTraceHomology.comparison R Y X f U g g
  have h₂ := ModuleCech.PushforwardNaturality.cohomology_naturality R X (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) i
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R)) (FiniteEtale.ModuleTrace.trace R Y X f g) g
  exact (congrArg (fun z => z ≫ (TopFormTrace.serreIso X i g).hom) h₁).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (ModuleTraceHomology.pushforwardIso R Y X f U g g).hom ≫ z) h₂).trans
        (Category.assoc _ _ _).symm))

variable [SmoothOfRelativeDimension g Y.hom] [Smooth Y.hom] [IsProper Y.hom]

variable [GeometricallyConnected Y.hom]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)

def traceIso : cohomology X Y f i g ≃+ Projective.TopTracePairing.coefficientRing R :=
  ((serreIso X Y f i g) ≪≫ FiniteEtale.ProperTraceBase.traceIso X Y f i B hB g s hs).addCommGroupIsoToAddEquiv

omit [Smooth X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g Y.hom] in
theorem traceIso_apply (x : cohomology X Y f i g) :
    traceIso X Y f i B hB g s hs x = trace X Y f i B hB g x := by
  change ((serreIso X Y f i g).hom ≫ (FiniteEtale.ProperTraceBase.traceIso X Y f i B hB g s hs).hom) x = _
  rw [FiniteEtale.ProperTraceBase.traceIso_hom]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite
