import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Total Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopy.CechTotalHomotopy

noncomputable section

/-! Homotopic maps of actual presheaf complexes induce equal Cech total cohomology maps in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} {f g : K ⟶ L}
  (h : Homotopy f g)

include h in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E f) i =
    HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E g) i :=
  Module.TotalHomotopy.ModuleTotalHomotopy.homology ((FormalCoproduct.cochainComplexFunctor E).mapHomotopy h) i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopy.CechTotalHomotopy
