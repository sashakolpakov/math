import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction

/-! # Crystalline Product Identity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineProductIdentity.CM

noncomputable section

/-! The H1 group law follows from the axis-map identity on the base-changed
product. All comparison isomorphisms here are canonical scheme pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductEndomorphisms.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction.CM.End

variable (q : ℕ) [Fact q.Prime]

theorem pullback_conjugate {X Y : Over (Spec (.of (ZMod q)))}
    (e : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ e.hom = e.hom ≫ g) :
    (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q e.inv).comp ((NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f).comp (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q e.hom)) =
      NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q g := by
  rw [CrystallineFunctoriality.CM.rationalPullback_comp, CrystallineFunctoriality.CM.rationalPullback_comp, h, Iso.inv_hom_id_assoc]

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (b : Spec (.of (ZMod q)) ⟶ S)

local notation "PB" => Over.pullback b
local instance : GrpObj ((PB).obj A) := Functor.grpObjObj (F := Over.pullback b)
local instance : IsCommMonObj ((PB).obj A) := Functor.isCommMonObj_obj (F := Over.pullback b)

theorem groupLaw_of_axis_identity
    (hfold : NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q ((PB).map (ProductEndomorphisms.CM.fold A)) =
      NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q ((PB).map (ProductEndomorphisms.CM.left A)) + NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q ((PB).map (ProductEndomorphisms.CM.right A))) :
    CrystallineMonoidAction.CM.End.GroupLawIdentity q ((PB).obj A) := by
  let G := (PB).obj A
  let e := ProductEndomorphisms.CM.productBaseChange A b
  have hc : NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (ProductEndomorphisms.CM.fold G) = NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (ProductEndomorphisms.CM.left G) + NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (ProductEndomorphisms.CM.right G) := by
    rw [← pullback_conjugate q e ((PB).map (ProductEndomorphisms.CM.fold A)) (ProductEndomorphisms.CM.fold G) (ProductEndomorphisms.CM.fold_baseChange A b),
      hfold, LinearMap.add_comp, LinearMap.comp_add,
      pullback_conjugate q e ((PB).map (ProductEndomorphisms.CM.left A)) (ProductEndomorphisms.CM.left G) (ProductEndomorphisms.CM.left_baseChange A b),
      pullback_conjugate q e ((PB).map (ProductEndomorphisms.CM.right A)) (ProductEndomorphisms.CM.right G) (ProductEndomorphisms.CM.right_baseChange A b)]
  have hm := congrArg (fun f => f.comp (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (fst G G))) hc
  change NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q μ[G] = NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (fst G G) + NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (snd G G)
  simpa only [LinearMap.add_comp, CrystallineFunctoriality.CM.rationalPullback_comp, ProductEndomorphisms.CM.fold_fst, ProductEndomorphisms.CM.left_fst, ProductEndomorphisms.CM.right_fst] using hm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineProductIdentity.CM
