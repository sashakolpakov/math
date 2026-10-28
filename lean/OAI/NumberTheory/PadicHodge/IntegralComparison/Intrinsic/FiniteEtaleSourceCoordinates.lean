import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleProperTraceBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleOrderedPushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardCoordinateIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeOrderedReindexComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Source

/-! # Finite Etale Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleSourceCoordinates

noncomputable section

/-! The actual two-stage finite Serre isomorphism returns to the
original source single-sheaf coordinate under the literal ordered
projection from native module Cech cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.TopologicalSpace _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  (c g : ℕ) [SmoothOfRelativeDimension g X.hom] [Smooth X.hom] [IsProper X.hom]
  [GeometricallyConnected X.hom]

abbrev forms := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
abbrev coefficient := (Scheme.Modules.pushforward f.left).obj (forms Y g)
abbrev ambientCover := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
abbrev baseCover := TopFormTrace.cover X i
abbrev sourceCover := IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R Y X f (baseCover X i)

local instance i_limits : PreservesFiniteLimits (Opens.map i.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass i.left.base.frameHom).toFunctor
  infer_instance
local instance f_limits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance
local instance comp_limits : PreservesFiniteLimits (Opens.map (f.left ≫ i.left).base) := by
  change PreservesFiniteLimits (OrderHom.ofClass (f.left ≫ i.left).base.frameHom).toFunctor
  infer_instance

abbrev sourceCoordinates :=
  (ModuleCech.CohomologyNaturality.forgetHomologyIso R Y (sourceCover X Y f i) (forms Y g) g).hom ≫
    homologyMap (OrderedCech.Projection.map (sourceCover X Y f i) (forms Y g).presheaf) g ≫
      (PrincipalSource.PushforwardCoordinates.globalCoordinates f.left i.left (ambientCover (R := R) (n := n))
        (forms Y g) c g).inv

omit [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [SmoothOfRelativeDimension g X.hom] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem comparison :
    (EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g).hom ≫
      PrincipalReference.Source.ReferenceComparison.sourceOutput f.left i.left
        (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom (ambientCover (R := R) (n := n)) (forms Y g) c g =
    sourceCoordinates X Y f i c g := by
  have hd :
      (ModuleCech.Pushforward.Comparison.cohomologyIso R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i (coefficient X Y f g)
        (ambientCover (R := R) (n := n)) g).hom ≫
        (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom
          (ambientCover (R := R) (n := n))
          ((Scheme.Modules.pushforward i.left).obj (coefficient X Y f g)) g).hom =
      (ModuleCech.CohomologyNaturality.forgetHomologyIso R X (baseCover X i) (coefficient X Y f g) g).hom ≫
        homologyMap (OrderedCech.Projection.map (baseCover X i) (coefficient X Y f g).presheaf) g ≫
        homologyMap (OrderedCech.Reindex.iso (Opens.map i.left.base)
          (ambientCover (R := R) (n := n)) (coefficient X Y f g).presheaf).inv g :=
    ModuleCech.PushforwardCoordinateIso.comparison R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i
      (coefficient X Y f g) (ambientCover (R := R) (n := n)) g
  have hc :
      homologyMap (OrderedCech.Reindex.iso (Opens.map i.left.base)
        (ambientCover (R := R) (n := n)) (coefficient X Y f g).presheaf).inv g ≫
      homologyMap (OrderedCech.Reindex.iso (Opens.map (f.left ≫ i.left).base)
        (ambientCover (R := R) (n := n)) (forms Y g).presheaf).hom g =
      homologyMap (OrderedCech.Reindex.iso (Opens.map f.left.base) (baseCover X i)
        (forms Y g).presheaf).hom g :=
    SchemeOrderedReindexComposition.homology f.left i.left (forms Y g)
      (ambientCover (R := R) (n := n)) g
  have h := congrArg (fun a =>
      (ModuleTraceHomology.pushforwardIso R Y X f (baseCover X i) g g).hom ≫ a ≫
        homologyMap (OrderedCech.Reindex.iso (Opens.map (f.left ≫ i.left).base)
          (ambientCover (R := R) (n := n)) (forms Y g).presheaf).hom g) hd
  simp only [Category.assoc] at h
  rw [hc] at h
  have hf := ModuleOrderedPushforward.comparison R Y X f (baseCover X i) g g
  have ht := h.trans hf
  have out := congrArg (fun a => a ≫
    (PrincipalSource.PushforwardCoordinates.globalCoordinates f.left i.left (ambientCover (R := R) (n := n))
      (forms Y g) c g).inv) ht
  simp only [EtaleProperTraceBase.IntrinsicFinite.serreIso, Iso.trans_hom,
    PrincipalReference.Source.ReferenceComparison.sourceOutput,
    PrincipalSource.PushforwardCoordinates.outputCoordinates,
    PrincipalSource.PushforwardCoordinates.reindex, sourceCoordinates, Category.assoc] at out ⊢
  convert out using 1
  as_aux_lemma => rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleSourceCoordinates
