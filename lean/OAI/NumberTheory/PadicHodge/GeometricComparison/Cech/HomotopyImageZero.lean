import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopyOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalMapFunctor

/-! # Homotopy Image Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.HomotopyImageZero.CechHomotopyImageZero

noncomputable section

/-! A vanishing image in a homotopy comparison remains zero on the
original Cech total H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {K L M N : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (t : K ⟶ L) (a : L ⟶ N) (b : N ⟶ N) (g : L ⟶ M) (d : M ⟶ N)
  (h : Homotopy (a ≫ b) (g ≫ d)) (hz : t ≫ g = 0)

include h hz in
theorem homology_raw : HomologicalComplex.homologyMap
    (TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E (t ≫ a ≫ b)) 1 = 0 := by
  let F := TotalMapFunctor.CechTotalMapFunctor.functor.{u, v} R E
  have he := TotalHomotopyOne.CechTotalHomotopyHOne.homology.{u, v, s, t} R E
    (HomotopyImage.HomotopyImageZero.homotopy t a b g d h hz)
  change HomologicalComplex.homologyMap (F.map (t ≫ a ≫ b)) 1 =
    HomologicalComplex.homologyMap (F.map (0 : K ⟶ N)) 1 at he
  exact he.trans ((congrArg (fun q => HomologicalComplex.homologyMap q 1) (F.map_zero K N)).trans
    (HomologicalComplex.homologyMap_zero (F.obj K) (F.obj N) 1))

include h hz in
theorem homology :
    HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E t) 1 ≫
      HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E a) 1 ≫
        HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E b) 1 = 0 := by
  let F := TotalMapFunctor.CechTotalMapFunctor.functor.{u, v} R E
  change HomologicalComplex.homologyMap (F.map t) 1 ≫
    HomologicalComplex.homologyMap (F.map a) 1 ≫ HomologicalComplex.homologyMap (F.map b) 1 = 0
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← F.map_comp, ← F.map_comp]
  exact homology_raw.{u, v, s, t} R E t a b g d h hz

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.HomotopyImageZero.CechHomotopyImageZero
