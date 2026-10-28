import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.TotalLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CohomologyCup

/-! # Algebraic Smooth Cohomology Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCohomologyProduct.Cech

noncomputable section

/-! The actual algebraic-to-smooth map preserves the product on
the original categorical Čech cohomology groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (X : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (N : SimplicialObject (FormalCoproduct.{0} X.left.Opens))

def cohomologyCup (p q : ℕ) :
    (AlgebraicSmoothCechProduct.smoothTotal X N).homology p →ₗ[ℂ] (AlgebraicSmoothCechProduct.smoothTotal X N).homology q →ₗ[ℂ]
      (AlgebraicSmoothCechProduct.smoothTotal X N).homology (p + q) :=
  Cochain.CohomologyCup.cohomologyCup (AlgebraicSmoothCechProduct.smoothTotal X N) (AlgebraicSmoothCechProduct.totalPairing X N)
    (IntegralComparison.Smooth.TotalLeibniz.AlgebraicCechProduct.differential_totalPairing X N) p q

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] in
theorem rational_cohomologyCup_eq (p q : ℕ) :
    RationalDeRham.CohomologyCup.Cech.cohomologyCup ℂ X N p q =
      Cochain.CohomologyCup.cohomologyCup (RationalDeRham.TotalCup.Cech.total ℂ X N)
        (RationalDeRham.TotalCup.Cech.totalCup ℂ X N)
        (RationalDeRham.TotalLeibniz.CechCup.differential_totalCup ℂ X N) p q := rfl

theorem totalMap_cohomologyCup (p q : ℕ)
    (x : (RationalDeRham.TotalCup.Cech.total ℂ X N).homology p)
    (y : (RationalDeRham.TotalCup.Cech.total ℂ X N).homology q) :
    HomologicalComplex.homologyMap (AlgebraicSmoothCechProduct.totalMap X N) (p + q)
        (RationalDeRham.CohomologyCup.Cech.cohomologyCup ℂ X N p q x y) =
      cohomologyCup X N p q (HomologicalComplex.homologyMap (AlgebraicSmoothCechProduct.totalMap X N) p x)
        (HomologicalComplex.homologyMap (AlgebraicSmoothCechProduct.totalMap X N) q y) := by
  rw [rational_cohomologyCup_eq]
  exact Cochain.CupNaturality.Cohomology.cohomologyMap_cup
    (RationalDeRham.TotalCup.Cech.totalCup ℂ X N) (AlgebraicSmoothCechProduct.totalPairing X N)
    (RationalDeRham.TotalLeibniz.CechCup.differential_totalCup ℂ X N)
    (IntegralComparison.Smooth.TotalLeibniz.AlgebraicCechProduct.differential_totalPairing X N) (AlgebraicSmoothCechProduct.totalMap X N) (AlgebraicSmoothCechProduct.totalMap_pairing X N) p q x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCohomologyProduct.Cech
