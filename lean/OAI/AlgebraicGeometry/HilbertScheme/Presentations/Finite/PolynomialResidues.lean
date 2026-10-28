import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TopResidue
import Mathlib.RingTheory.Finiteness.Basic

/-! # Polynomial Residues -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialResidues.ProjectiveCech

noncomputable section

/-! Homogeneous polynomial Čech residues lie in an explicit finite coefficient module. -/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]

def polynomialResidueCoefficientModule (d : ℤ) : Submodule R ((σ → ℤ) →₀ R) :=
  Finsupp.supported R R {a | LaurentDegree.ProjectiveCech.exponentDegree a = d ∧ ∀ i, a i < 0}

def polynomialResidueCoefficientEquiv (d : ℤ) :
    polynomialResidueCoefficientModule (σ := σ) R d ≃ₗ[R] (NegativeDegree.ProjectiveCech.NegativeDegreeExponents (σ := σ) d →₀ R) :=
  Finsupp.supportedEquivFinsupp _

instance polynomialResidueCoefficient_finite (d : ℤ) :
    Module.Finite R (polynomialResidueCoefficientModule (σ := σ) R d) := by
  let : Fintype (NegativeDegree.ProjectiveCech.NegativeDegreeExponents (σ := σ) d) := Fintype.ofFinite _
  exact Module.Finite.of_surjective (polynomialResidueCoefficientEquiv (σ := σ) R d).symm.toLinearMap
    (polynomialResidueCoefficientEquiv (σ := σ) R d).symm.surjective

def polynomialResidueAssembly (d : ℤ) :
    polynomialResidueCoefficientModule (σ := σ) R d →ₗ[R] Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R :=
  LinearMap.pi (fun s => if s = Finset.univ then
    (LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s).comp (polynomialResidueCoefficientModule (σ := σ) R d).subtype else 0)

theorem polynomialTopResidue_mem_finite_range (d : ℤ) (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Polynomial.Cech.ProjectiveCech.CechHomogeneous R d f) : Polynomial.TopResidue.ProjectiveCech.polynomialTopResidue R f ∈ (polynomialResidueAssembly (σ := σ) R d).range := by
  have hc : Polynomial.TopResidue.ProjectiveCech.polynomialTopResidueCoefficients R f Finset.univ ∈ polynomialResidueCoefficientModule (σ := σ) R d := by
    intro a ha
    obtain ⟨hasupport, haneg⟩ := Finset.mem_filter.mp ha
    refine ⟨?_, fun i => lt_of_not_ge (fun hi => haneg ⟨i, hi⟩)⟩
    by_contra hd
    exact (Finsupp.mem_support_iff.mp hasupport)
      (LaurentCoordinates.ProjectiveCech.chartCoordinates_degree R Finset.univ d _ (hf Finset.univ) a hd)
  refine ⟨⟨Polynomial.TopResidue.ProjectiveCech.polynomialTopResidueCoefficients R f Finset.univ, hc⟩, ?_⟩
  funext s
  by_cases hs : s = Finset.univ
  · subst s
    simp only [polynomialResidueAssembly, LinearMap.pi_apply]
    rfl
  · simp only [polynomialResidueAssembly, LinearMap.pi_apply, ite_eq_right hs, LinearMap.zero_apply]
    exact (Polynomial.TopResidue.ProjectiveCech.polynomialTopResidue_of_not_univ R f s hs).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialResidues.ProjectiveCech
