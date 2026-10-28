import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarCoordinates

/-! # Scalar Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarValue

noncomputable section

/-! The fixed projective point scalar factors through its intrinsic
ambient oriented-purity coordinate, with an arbitrary line frame. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalCoordinates
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarCoordinates OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
  ScalarCoordinates.line_qc
variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion f] (z : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion z]
  (hbase : z ≫ (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (z ≫ f) ⁻¹ᵁ U)
  (i : Fin (n+2)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (e : Γ(ScalarCoordinates.line (R := R) (n := n), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)]
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    (z ≫ f).ker.ideal ⟨U,hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))
  (y : (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t)
    (c+m)).obj (LocalCoordinates.principalDual f z B U hU))

local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U

def coordinate : R := by
  let hprojective : ∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj ((Survivor.complex f z B).X q)) :=
    fun q => ScalarCoordinates.source_projective f z B U hU i hi q
  let hterms : ∀ q, ((Affine.LinearResolutionPurity.internalComplex
      (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B)).X q).IsQuasicoherent :=
    fun q => ScalarCoordinates.dual_qc f z B hB q
  exact (ScalarCoordinates.quotient f z hbase U hU hcontains)
    ((Affine.OrientedPurity.iso U hU (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B)
      (Survivor.coefficient f z) (IntegralComparison.Projective.NegativeResolution.augmentation (Survivor.coefficient f z) (Survivor.chart (R := R)) B)
      ((z ≫ f).ker.ideal ⟨U,hU⟩) (ScalarCoordinates.quotientIso f z U hU) (Fin.append s t)
      ((KoszulPoint.Resolution.Comparison.full_ideal
        Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t).trans hst) hreg
      (Principal.OrientedResidueNormalizationBase.lineIso U hU (ScalarCoordinates.line (R := R) (n := n)) e)).hom
        ((Principal.ProductPointCoordinates.sectionIso U hU
          (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B) (c+m)).inv
            (homologyMap (AugmentedOrdered.CechForget.forgetSupport (PrincipalPoint.Fraction.family U t)
              (LocalCoordinates.principalDual f z B U hU)) (c+m) y)))

attribute [local irreducible] PrincipalPoint.FrameScalar.value
  Affine.OrientedPurity.iso Principal.ProductPointCoordinates.sectionIso

theorem value_eq : ScalarCoordinates.value f z hbase B hB U hU hcontains i hi e s t hst hreg y =
    coordinate f z hbase B hB U hU hcontains i hi e s t hst hreg y := by
  let hprojective : ∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj ((Survivor.complex f z B).X q)) :=
    fun q => ScalarCoordinates.source_projective f z B U hU i hi q
  let hterms : ∀ q, ((Affine.LinearResolutionPurity.internalComplex
      (ScalarCoordinates.line (R := R) (n := n)) (Survivor.complex f z B)).X q).IsQuasicoherent :=
    fun q => ScalarCoordinates.dual_qc f z B hB q
  dsimp only [ScalarCoordinates.value, coordinate]
  exact PrincipalPoint.FrameScalar.value_eq U hU (ScalarCoordinates.line (R := R) (n := n))
    (Survivor.coefficient f z) (Survivor.complex f z B)
    (IntegralComparison.Projective.NegativeResolution.augmentation (Survivor.coefficient f z) (Survivor.chart (R := R)) B)
    ((z ≫ f).ker.ideal ⟨U,hU⟩) (ScalarCoordinates.quotientIso f z U hU) (ScalarCoordinates.quotient f z hbase U hU hcontains)
    e s t hreg hst (PrincipalPoint.Fraction.family U t) (n+1)
    (ScalarFraction.pure f z hbase B hB U hU)
    (ScalarFraction.zero f z hbase B hB U hU s t hst) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarValue
