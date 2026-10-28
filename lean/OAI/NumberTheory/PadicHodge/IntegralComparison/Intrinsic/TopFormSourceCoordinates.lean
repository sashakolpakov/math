import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.IdentitySourceCoordinates

/-! # Top Form Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormSourceCoordinates

noncomputable section

/-! The smooth Serre isomorphism and original principal output retain
the literal native top-form class in single-sheaf coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.TopologicalSpace _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  (c g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [GeometricallyConnected X.hom]

abbrev forms := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
abbrev ambientCover := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
abbrev cover := TopFormTrace.cover X i

abbrev sourceCoordinates :=
  (ModuleCech.CohomologyNaturality.forgetHomologyIso R X (cover X i) (forms X g) g).hom ≫
    homologyMap (OrderedCech.Projection.map (cover X i) (forms X g).presheaf) g ≫
      (PrincipalSource.PushforwardCoordinates.globalCoordinates (𝟙 X.left) i.left
        (ambientCover (R := R) (n := n)) (forms X g) c g).inv

omit [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsClosedImmersion (Over.Hom.left i)] [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem comparison :
    (TopFormTrace.serreIso X i g).hom ≫
      PrincipalReference.Source.ReferenceComparison.sourceOutput (𝟙 X.left) i.left
        (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom (ambientCover (R := R) (n := n)) (forms X g) c g =
    sourceCoordinates X i c g :=
  ModuleCech.IdentitySourceCoordinates.comparison R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i
    (forms X g) (ambientCover (R := R) (n := n)) c g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormSourceCoordinates
