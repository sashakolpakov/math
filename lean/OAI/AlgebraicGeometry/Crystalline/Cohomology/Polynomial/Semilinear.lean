import OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyBijective

/-! # Semilinear -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Semilinear.PolynomialSemilinearCohomology

noncomputable section

/-! # Bijectivity of the semilinear completed-polynomial cohomology operator -/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p] [Fintype σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius.complex p k σ
local notation "φ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius.scalarEquiv p k

def frobenius (n : ℕ) : (C).homology n →ₛₗ[(φ).toRingHom] (C).homology n :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap
    (RationalPolynomial.RationalPolynomialCoefficientFrobenius.frobenius p k σ) n

theorem frobenius_bijective (n : ℕ) : Function.Bijective (frobenius p k σ n) :=
  Semilinear.HomologyBijective.SemilinearHomologyBijective.homology_bijective (RationalPolynomial.RationalPolynomialCoefficientFrobenius.frobenius p k σ) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Semilinear.PolynomialSemilinearCohomology
