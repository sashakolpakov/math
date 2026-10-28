import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Point Formula Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport.CM

noncomputable section

/-! Transport pointwise neighbor sums along actual source and group
isomorphisms. Source multisets are reindexed without changing multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {S : Scheme} (G H : CommGrp (Over S)) (e : G.X ≅ H.X) [IsMonHom e.hom]
  (T : Over S)

def postcomposeAddEquiv : Additive (T ⟶ G.X) ≃+ Additive (T ⟶ H.X) where
  toFun x := Additive.ofMul (x.toMul ≫ e.hom)
  invFun x := Additive.ofMul (x.toMul ≫ e.inv)
  left_inv x := by
    apply Additive.toMul.injective
    exact (Category.assoc _ _ _).trans
      ((congrArg (x.toMul ≫ ·) e.hom_inv_id).trans (Category.comp_id _))
  right_inv x := by
    apply Additive.toMul.injective
    exact (Category.assoc _ _ _).trans
      ((congrArg (x.toMul ≫ ·) e.inv_hom_id).trans (Category.comp_id _))
  map_add' x y := MonObj.mul_comp x.toMul y.toMul e.hom

theorem postcompose_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) (x : Additive (T ⟶ G.X)) :
    postcomposeAddEquiv G H e T (PointSpecializationFormula.CM.Points.evaluateAt G T f x) =
      PointSpecializationFormula.CM.Points.evaluateAt H T (EndTransportCM.CM.transport e f) (postcomposeAddEquiv G H e T x) :=
  (EndTransportCM.CM.transport_points e T x.toMul f).symm

variable {X Y : Over S} (u : X ≅ Y) (a : X ⟶ G.X) (b : Y ⟶ H.X)
  (hnatural : a ≫ e.hom = u.hom ≫ b)

include hnatural

theorem postcompose_source_point (x : T ⟶ X) :
    postcomposeAddEquiv G H e T (Additive.ofMul (x ≫ a)) =
      Additive.ofMul ((x ≫ u.hom) ≫ b) := by
  apply Additive.toMul.injective
  exact (Category.assoc x a e.hom).trans
    ((congrArg (x ≫ ·) hnatural).trans (Category.assoc x u.hom b).symm)

theorem postcompose_neighbor_sum (N : Multiset (T ⟶ Y)) :
    postcomposeAddEquiv G H e T
      ((N.map (fun z => Additive.ofMul ((z ≫ u.inv) ≫ a))).sum) =
        (N.map (fun z => Additive.ofMul (z ≫ b))).sum := by
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z _
  dsimp only [Function.comp_def]
  rw [postcompose_source_point G H e T u a b hnatural]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem transported_neighbor_formula (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : T ⟶ X) (Nx Ny : Multiset (T ⟶ Y))
    (h : PointSpecializationFormula.CM.Points.evaluateAt H T (EndTransportCM.CM.transport e f)
      (Additive.ofMul ((x ≫ u.hom) ≫ b) - Additive.ofMul ((y ≫ u.hom) ≫ b)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ b))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ b))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt G T f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul ((z ≫ u.inv) ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul ((z ≫ u.inv) ≫ a))).sum := by
  apply (postcomposeAddEquiv G H e T).injective
  rw [postcompose_evaluate]
  simpa only [map_sub, postcompose_source_point G H e T u a b hnatural,
    postcompose_neighbor_sum G H e T u a b hnatural] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport.CM
