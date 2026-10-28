import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Quasi Finite Points -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.QuasiFinitePoints.Abelian

noncomputable section

/-! Points above closed arithmetic coordinates descend whenever the
coordinate map has discrete scheme fibers, in particular for etale charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem closed_point_of_quasiFinite_closed_image {X Y : Scheme}
    (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) (hx : IsClosed {f x}) : IsClosed {x} := by
  let V := f ⁻¹' {f x}
  have hV : IsClosed V := hx.preimage f.continuous
  let : DiscreteTopology V := isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f x))
  let xV : V := ⟨x, rfl⟩
  simpa only [Set.image_singleton] using hV.isClosedMap_subtype_val {xV} isClosed_singleton

theorem complex_point_descends_of_quasiFinite_closed_coordinates
    {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    (q : Y ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType q]
    (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (hp : IsClosed {(p ≫ f) (IsLocalRing.closedPoint ℂ)}) :
    ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
      Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p :=
  AlgebraicPoints.Abelian.complex_point_descends_of_closed (f ≫ q) p
    (closed_point_of_quasiFinite_closed_image f (p (IsLocalRing.closedPoint ℂ)) hp)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.QuasiFinitePoints.Abelian
