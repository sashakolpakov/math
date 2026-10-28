import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

/-! # Dual Map Congruence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMapCongruence

/-! Equality of group morphisms respects the dependent represented dual construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

theorem representedDualMap_congr {S : Scheme.{u}} {A B DA DB : Over S} [GrpObj A] [GrpObj B]
    (HA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy DA)
    (HB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy DB)
    (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (h : f = g) :
    DualMaps.representedDualMap HA HB f = DualMaps.representedDualMap HA HB g := by
  cases h
  rfl

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMapCongruence
