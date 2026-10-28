import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightedTheta
import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCovariance
import OAI.AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion

/-! # Derivative Factorization Definitions -/

namespace OAI.RepresentationTheory.Theta.DerivativeFactorizationDefinitions

noncomputable section

/-!
Definitions reproduced from the committed DerivativeFactorization specification in a unique
namespace. No theorem stubs are imported. The trace coordinates and the bare
Weil/Poisson equation remain supplied interfaces as in that specification.
-/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

abbrev AQf := IsDedekindDomain.FiniteAdeleRing ℤ ℚ
abbrev AQ := NumberField.AdeleRing ℤ ℚ

/-- Schwartz–Bruhat functions on a finite-adelic position space. -/
abbrev FiniteSchwartz (X : Type*) [TopologicalSpace X] :=
  { φ : X → ℂ // IsLocallyConstant φ ∧ HasCompactSupport φ }

abbrev Input (ι : Type*) := FiniteSchwartz (ι → AQf)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def diagonal (x : ι → ℚ) : ι → AQf :=
  fun i => algebraMap ℚ AQf (x i)

def realPosition (x : ι → ℚ) : ι → ℝ :=
  fun i => (x i : ℝ)

/-- The manuscript's Gaussian with its linear Jacobi term. -/
def kernel (B : Matrix ι ι ℂ)
    (x : ι → ℚ) (z : ι → ℂ) : ℂ :=
  Complex.exp
    ((Real.pi : ℂ) * Complex.I *
        AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm B (realPosition x) (realPosition x) +
      (2 * (Real.pi : ℂ) * Complex.I) *
        AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι (realPosition x) z)

def theta (φ : Input ι)
    (B : Matrix ι ι ℂ) (z : ι → ℂ) : ℂ :=
  ∑' x : ι → ℚ, φ.1 (diagonal x) * kernel B x z

def completed (φ : Input ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z * theta φ Z.matrix z

def firstCoefficient (φ : Input ι)
    (B : Matrix ι ι ℂ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑' x : ι → ℚ,
    φ.1 (diagonal x) •
      AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
        (realPosition x) (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm B)

abbrev AFf (F : Type*) [Field F] [NumberField F] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 F) F

abbrev AF (F : Type*) [Field F] [NumberField F] :=
  NumberField.AdeleRing (𝓞 F) F

end

end OAI.RepresentationTheory.Theta.DerivativeFactorizationDefinitions
