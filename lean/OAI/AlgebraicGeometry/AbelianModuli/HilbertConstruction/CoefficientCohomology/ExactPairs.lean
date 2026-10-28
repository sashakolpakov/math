import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ConnectingMap

/-! # Exact Pairs -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs.ZariskiCohomology

noncomputable section

/-! The three exact pairs in the genuine long cohomology sequence retain their prescribed linear coefficient actions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

theorem coefficientCohomology_exact_middle (n : ℕ) :
    Function.Exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map S.f).hom
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map S.g).hom := by
  intro x
  constructor
  · exact Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₂_explicit
      (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n x
  · rintro ⟨y, rfl⟩
    exact Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_comp_zero₂
      (S := S.map (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n y

theorem coefficientCohomology_exact_right (n : ℕ) :
    Function.Exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map S.g).hom
      (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS n).hom := by
  intro x
  constructor
  · exact Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₃_explicit
      (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n (n + 1) rfl x
  · rintro ⟨y, rfl⟩
    exact Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_comp_zero₃
      (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n (n + 1) rfl y

theorem coefficientCohomology_exact_left (n : ℕ) :
    Function.Exact (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS n).hom
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map S.f).hom := by
  intro x
  constructor
  · exact Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₁_explicit
      (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n (n + 1) rfl x
  · rintro ⟨y, rfl⟩
    exact Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_comp_zero₁
      (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n (n + 1) rfl y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs.ZariskiCohomology
