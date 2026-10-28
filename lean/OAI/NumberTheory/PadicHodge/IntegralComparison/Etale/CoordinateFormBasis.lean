import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactDifferentialBasis
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Coordinate Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis

noncomputable section

/-!
# IntegralComparison: native differential-form bases on étale polynomial charts
-/

universe u

variable (R C σ : Type u) [CommRing R] [CommRing C] [Algebra R C]
  [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra.FormallyEtale (MvPolynomial σ R) C]

def coordinate (i : σ) : C := algebraMap (MvPolynomial σ R) C (MvPolynomial.X i)

def kaehlerBasis : Module.Basis σ C (KaehlerDifferential R C) :=
  ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange C).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial σ R) C)

theorem kaehlerBasis_apply (i : σ) :
    kaehlerBasis R C σ i = KaehlerDifferential.D R C (coordinate R C σ i) := by
  rw [kaehlerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact ((LinearEquiv.symm_apply_eq
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial σ R) C)).mp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R (MvPolynomial σ R) C
      (MvPolynomial.X i))).symm

variable [LinearOrder σ]

def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R C n) :=
  ExactDifferentialBasis.basis R C σ (coordinate R C σ) n (kaehlerBasis R C σ)
    (kaehlerBasis_apply R C σ)

theorem basis_apply (n : ℕ) (s : Set.powersetCard σ n) : basis R C σ n s =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R C 1 (fun j => coordinate R C σ (Set.powersetCard.ofFinEmbEquiv.symm s j)) :=
  ExactDifferentialBasis.basis_apply R C σ (coordinate R C σ) n (kaehlerBasis R C σ)
    (kaehlerBasis_apply R C σ) s

def exteriorEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R C n ≃ₗ[C] ⋀[C]^n (KaehlerDifferential R C) :=
  ExactDifferentialBasis.exteriorEquiv R C σ (coordinate R C σ) n (kaehlerBasis R C σ)
    (kaehlerBasis_apply R C σ)

theorem exteriorEquiv_eq (n : ℕ) : (exteriorEquiv R C σ n).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R C n :=
  ExactDifferentialBasis.exteriorEquiv_eq R C σ (coordinate R C σ) n (kaehlerBasis R C σ)
    (kaehlerBasis_apply R C σ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
