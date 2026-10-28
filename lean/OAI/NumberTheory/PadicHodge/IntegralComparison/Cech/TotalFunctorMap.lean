import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Total Functor Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TotalFunctorMap

noncomputable section

/-! The original Cech total map is the map of the actual composite
bicomplex-total functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial
universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L)

theorem map :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.bicomplex R E ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)).map a =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R E a := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TotalFunctorMap
