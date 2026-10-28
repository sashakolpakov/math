import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport

/-! # Mapped Neighbor Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MappedNeighborFormula.CM

noncomputable section

/-! Push a full neighbor equation through the constructed source and
group isomorphisms, retaining the raw neighbor multiset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport.CM

variable {S : Scheme} (G H : CommGrp (Over S)) (e : G.X ≅ H.X) [IsMonHom e.hom]
  (T : Over S) {X Y : Over S} (u : X ≅ Y) (a : X ⟶ G.X) (b : Y ⟶ H.X)
  (hnatural : a ≫ e.hom = u.hom ≫ b)

include hnatural

theorem mapped_neighbor_formula (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : T ⟶ X) (Nx Ny : Multiset (T ⟶ X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt G T f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt H T (EndTransportCM.CM.transport e f)
      (Additive.ofMul ((x ≫ u.hom) ≫ b) - Additive.ofMul ((y ≫ u.hom) ≫ b)) =
      (Nx.map (fun z => Additive.ofMul ((z ≫ u.hom) ≫ b))).sum -
        (Ny.map (fun z => Additive.ofMul ((z ≫ u.hom) ≫ b))).sum := by
  have he := congrArg (PointFormulaTransport.CM.postcomposeAddEquiv G H e T) h
  rw [PointFormulaTransport.CM.postcompose_evaluate] at he
  simpa only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def,
    PointFormulaTransport.CM.postcompose_source_point G H e T u a b hnatural] using he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MappedNeighborFormula.CM
