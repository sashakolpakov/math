import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechHomotopyEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiLinearity

/-! # Zariski Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison

noncomputable section

/-! The bounded ordered coefficient Čech complex computes genuine Zariski cohomology in every positive degree on affine covers of separated schemes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

def orderedCechZariskiModuleIso {X : Scheme.{u}} [X.IsSeparated]
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).homology (n + 1) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj M :=
  (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U (n + 1)).symm ≪≫
    CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso c M U hU haffine n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison
