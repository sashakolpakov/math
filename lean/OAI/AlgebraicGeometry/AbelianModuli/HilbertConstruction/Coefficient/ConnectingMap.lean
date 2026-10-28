import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.ConnectingHomomorphism

/-! # Connecting Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ConnectingMap.ZariskiCohomology

noncomputable section

/-! Connecting homomorphisms are actual linear morphisms between canonical coefficient cohomology modules. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def coefficientConnectingMap {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₃ ⟶
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj S.X₁ :=
  ModuleCat.homMk (AddCommGrpCat.ofHom (Zariski.ConnectingHomomorphism.ZariskiCohomology.cohomologyConnecting hS n)) (by
    intro r
    apply ConcreteCategory.hom_ext
    intro x
    exact (Zariski.ConnectingHomomorphism.ZariskiCohomology.cohomologyConnecting_coefficient_smul c hS n r x).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ConnectingMap.ZariskiCohomology
