import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFrameValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.AmbientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalFrameNormalization

/-! # Scalar Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarIndependence

noncomputable section

/-! The scalar extracted from the original projective point class is
independent of its full regular equations and their matching frame. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem append_comp {A B : Type*} {c m : ℕ} (f : A → B)
    (s : Fin c → A) (t : Fin m → A) :
    Fin.append (fun i => f (s i)) (fun i => f (t i)) =
      fun i => f (Fin.append s t i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right]

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (z : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion z]
  (hbase : z ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (z ≫ f) ⁻¹ᵁ U)
  (i : Fin (n+2)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  [IsArtinianRing R] [IsLocalRing R]
  [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  {c m : ℕ} (hcm : c+m=n+1)

local instance line_qc : (ScalarCoordinates.line (R := R) (n := n)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (Survivor.chart (R := R)) (n+2))
include i hi in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem source_projective (q : ℕ) :
    Projective ((AffineOpen.InternalHom.sections U hU).obj ((Survivor.complex f z B).X q)) :=
  Affine.ProjectiveResolutionTerms.term_projective U hU i hi (Survivor.coefficient f z)
    (Survivor.chart (R := R)) B q
include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem dual_qc (q : ℕ) :
    ((Affine.LinearResolutionPurity.internalComplex
      (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B)).X q).IsQuasicoherent :=
  PrincipalConcentration.terms_qc f z B hB q
local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U
include hU in
omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] in
theorem ambientSmooth : Algebra.Smooth R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) := by
  let : Smooth (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom := IntegralComparison.Projective.SpaceSmooth.smooth
  exact Intrinsic.SmoothClosedSections.smooth_sections R (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) U hU

variable (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (z ≫ f).ker.ideal ⟨U,hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))
  (b : Module.Basis (Fin (n+1)) Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    Ω[Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)⁄R])
  (hb : (fun a : Fin (c+m) => b (Fin.cast hcm a)) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (t a)))
  (s' : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t' : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst' : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s' t' =
    (z ≫ f).ker.ideal ⟨U,hU⟩)
  (hreg' : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s' t')))
  (bt : Module.Basis (Fin (n+1)) Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    Ω[Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)⁄R])
  (hbt : (fun a : Fin (c+m) => bt (Fin.cast hcm a)) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (s' a))
      (fun a => KaehlerDifferential.D R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (t' a)))

attribute [local irreducible] IntegralComparison.Projective.AmbientAdjunction.chartLineExterior
  ParameterLineAdjunction.frame Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame
  PrincipalPoint.FrameScalar.value

include hb hbt in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem value_independent
    (y : (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t)
      (c+m)).obj (LocalCoordinates.principalDual f z B U hU))
    (y' : (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t')
      (c+m)).obj (LocalCoordinates.principalDual f z B U hU))
    (hxy : homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t)
        (LocalCoordinates.principalDual f z B U hU)) (c+m) y =
      homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t')
        (LocalCoordinates.principalDual f z B U hU)) (c+m) y') :
    ScalarCoordinates.value f z hbase B hB U hU hcontains i hi
      (IntegralComparison.Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
        (Survivor.chart (R := R)) U hU i hi b) s t hst hreg
      y =
    ScalarCoordinates.value f z hbase B hB U hU hcontains i hi
      (IntegralComparison.Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
        (Survivor.chart (R := R)) U hU i hi bt) s' t' hst' hreg'
      y' := by
  let hprojective : ∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj ((Survivor.complex f z B).X q)) :=
    fun q => source_projective f z B U hU i hi q
  let hterms : ∀ q, ((Affine.LinearResolutionPurity.internalComplex
      (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B)).X q).IsQuasicoherent :=
    fun q => dual_qc f z B hB q
  let hsmooth : Algebra.Smooth R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) := ambientSmooth U hU
  have hind := Affine.PointFrameDimension.independent U hU
    (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B)
    (Survivor.coefficient f z)
    (IntegralComparison.Projective.NegativeResolution.augmentation (Survivor.coefficient f z) (Survivor.chart (R := R)) B)
    ((z ≫ f).ker.ideal ⟨U,hU⟩) (ScalarCoordinates.quotientIso f z U hU)
    (ScalarCoordinates.quotient f z hbase U hU hcontains) hcm
    (Fin.append s t) ((KoszulPoint.Resolution.Comparison.full_ideal
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t).trans hst)
    hreg b (hb.trans (append_comp (KaehlerDifferential.D R _) s t))
    (Fin.append s' t') ((KoszulPoint.Resolution.Comparison.full_ideal
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s' t').trans hst')
    hreg' bt (hbt.trans (append_comp (KaehlerDifferential.D R _) s' t'))
    (IntegralComparison.Projective.AmbientAdjunction.chartLineExterior i U hU hi (Survivor.chart (R := R)))
  have hframe :
      ScalarFrameValue.frameCoordinate f z hbase B hB U hU hcontains i hi
        s t hst hreg y b =
      ScalarFrameValue.frameCoordinate f z hbase B hB U hU hcontains i hi
        s' t' hst' hreg' y' bt := by
    dsimp only [ScalarFrameValue.frameCoordinate,
      ModuleFrame.coordinate,
      ScalarFrameValue.frame]
    exact congrArg₂ (fun a x => (ScalarCoordinates.quotient f z hbase U hU hcontains)
      (a ((Principal.ProductPointCoordinates.sectionIso U hU
        (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B) (c+m)).inv x)))
      hind hxy
  exact (ScalarFrameValue.value_eq f z hbase B hB U hU hcontains i hi
    s t hst hreg y b).trans (hframe.trans
      (ScalarFrameValue.value_eq f z hbase B hB U hU hcontains i hi
        s' t' hst' hreg' y' bt).symm)

include hb hbt in
omit [IsArtinianRing R] [IsLocalRing R] [IsProper (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem independent :
    ScalarCoordinates.value f z hbase B hB U hU hcontains i hi
      (IntegralComparison.Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
        (Survivor.chart (R := R)) U hU i hi b) s t hst hreg
      (LocalCoordinates.pointAt f z hbase B hB U hU s t hst hcm) =
    ScalarCoordinates.value f z hbase B hB U hU hcontains i hi
      (IntegralComparison.Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
        (Survivor.chart (R := R)) U hU i hi bt) s' t' hst' hreg'
      (LocalCoordinates.pointAt f z hbase B hB U hU s' t' hst' hcm) := by
  exact value_independent f z hbase B hB U hU hcontains i hi hcm
    s t hst hreg b hb s' t' hst' hreg' bt hbt
    (LocalCoordinates.pointAt f z hbase B hB U hU s t hst hcm)
    (LocalCoordinates.pointAt f z hbase B hB U hU s' t' hst' hcm)
    (AmbientCoordinates.independent f z hbase B hB U hU hcm s t hst s' t' hst')

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarIndependence
