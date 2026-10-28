import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CohomologyCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.ProductCongruence

/-! # Rational Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.RationalProduct.Cech

noncomputable section

/-! Over rational coefficients the integral Čech construction agrees
with the original product used in the geometric Betti comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))

theorem sectionPairing_eq_rational :
    CechProduct.sectionPairing R X = RationalDeRham.CechCup.sectionPairing R X := by
  funext a b U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact @WedgeNaturality.wedge_eq_rational R Γ(X.left, U.unop) _ _
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop)
    (RationalDeRham.CechCup.rationalSections R X U.unop) a b x y

variable (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

theorem totalCup_eq_rational (a b : ℕ) :
    CechProduct.totalCup R X N a b = RationalDeRham.TotalCup.Cech.totalCup R X N a b := by
  change Presheaf.TotalCup.CechProduct.totalCup N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
      (CechProduct.sectionPairing R X) a b =
    Presheaf.TotalCup.CechProduct.totalCup N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
      (RationalDeRham.CechCup.sectionPairing R X) a b
  rw [sectionPairing_eq_rational]

theorem cohomologyCup_eq_rational (a b : ℕ) :
    CechProduct.cohomologyCup R X N a b = RationalDeRham.CohomologyCup.Cech.cohomologyCup R X N a b := by
  apply Cochain.ProductCongruence.CohomologyCup.cohomologyCup_congr
  · exact RationalDeRham.TotalLeibniz.CechCup.differential_totalCup R X N
  · funext n m
    exact totalCup_eq_rational R X N n m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.RationalProduct.Cech
