import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalHomotopyOne

/-! # Total Homotopy One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopyOne.CechTotalHomotopyHOne

noncomputable section

/-! Homotopic maps of actual presheaf complexes induce equal H-one maps
after the original Cech bicomplex and first-quadrant totalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} {f g : K ⟶ L}
  (h : Homotopy f g)

include h in
theorem homology : HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E f) 1 =
    HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E g) 1 :=
  Module.TotalHomotopyOne.ModuleTotalHomotopyHOne.homology ((FormalCoproduct.cochainComplexFunctor E).mapHomotopy h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopyOne.CechTotalHomotopyHOne
