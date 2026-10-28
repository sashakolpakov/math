import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ModuleFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalFrameNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.FrameScalarValue

/-! # Scalar Frame Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFrameValue

noncomputable section

/-! The original projective scalar in its prescribed parameter frame is
the intrinsic oriented coordinate for that same differential basis. -/
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

variable (b : Module.Basis (Fin (n+1)) Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
  Ω[Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)⁄R])

def frame : (AffineOpen.InternalHom.sections U hU).obj (ScalarCoordinates.line (R := R) (n := n)) ≅
    ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  ParameterLineAdjunction.frame (c := n+1) (g := 0) b
    ((AffineOpen.InternalHom.sections U hU).obj (ScalarCoordinates.line (R := R) (n := n)))
    (Projective.AmbientAdjunction.chartLineExterior i U hU hi (Survivor.chart (R := R)))

attribute [local irreducible] ParameterLineAdjunction.frame
  Projective.AmbientAdjunction.chartLineExterior
  Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame

omit [IsNoetherianRing R] in
theorem scalarFrame_eq :
    Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
      (Survivor.chart (R := R)) U hU i hi b =
    Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame U hU
      (ScalarCoordinates.line (R := R) (n := n)) (frame U hU i hi b) := by
  dsimp only [Projective.PrincipalResidueCoordinates.scalarFrame,
    Projective.ParameterAdjunction.parameterFrame, frame,
    ScalarCoordinates.line, ScalarFraction.line]

def frameCoordinate : R :=
  ModuleFrame.coordinate f z hbase B hB U hU hcontains i hi
    (frame U hU i hi b) s t hst hreg y

attribute [local irreducible] frame ModuleFrame.coordinate
  ScalarCoordinates.value

theorem value_eq : ScalarCoordinates.value f z hbase B hB U hU hcontains i hi
      (Projective.PrincipalResidueCoordinates.scalarFrame (c := n+1) (g := 0)
        (Survivor.chart (R := R)) U hU i hi b) s t hst hreg y =
    frameCoordinate f z hbase B hB U hU hcontains i hi s t hst hreg y b := by
  dsimp only [frameCoordinate]
  rw [scalarFrame_eq]
  exact ModuleFrame.value_eq f z hbase B hB U hU hcontains i hi
    (frame U hU i hi b) s t hst hreg y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ScalarFrameValue
