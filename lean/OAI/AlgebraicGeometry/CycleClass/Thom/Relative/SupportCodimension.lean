import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Support Codimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SupportCodimension.Constructions

noncomputable section

/-! A support whose ambient codimension is one greater than a
containing integral support has a height-one generic point in that
actual reduced support, including in disconnected ambient presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

theorem point_lt_of_le_of_ne {S : Scheme} {x y : S} (h : x ≤ y) (hne : x ≠ y) : x < y := by
  rw [lt_iff_le_not_ge]
  exact ⟨h, fun hr => hne ((Scheme.le_iff_specializes.mp hr).antisymm
    (Scheme.le_iff_specializes.mp h)).eq⟩

theorem supportPreimage_coheight_one (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (B C : IrreducibleCloseds X.carrier) (hx : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (hd : X.supportCodimension C = X.supportCodimension B + 1) :
    Order.coheight (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hx) = 1 := by
  let S := Geometric.GenericPoint.reducedSupportScheme B
  let x : S := IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hx
  let η : S := genericPoint S
  have hyη (y : S) : y ≤ η := Scheme.le_iff_specializes.mpr (genericPoint_specializes y)
  have hη : Order.coheight η = 0 := Order.coheight_eq_zero.mpr (fun y _ => hyη y)
  have hmap : StrictMono (Geometric.GenericPoint.reducedSupportι B) := by
    intro s t hst
    exact point_lt_of_le_of_ne
      (Scheme.le_iff_specializes.mpr
        ((Scheme.le_iff_specializes.mp hst.le).map (Geometric.GenericPoint.reducedSupportι B).continuous))
      (fun h => hst.ne ((Geometric.GenericPoint.reducedSupportι B).isClosedEmbedding.injective h))
  have hηB : Geometric.GenericPoint.reducedSupportι B η = IntersectionGeometry.supportPoint B := Geometric.GenericPoint.reducedSupport_genericPoint_eq B
  have hxC : Geometric.GenericPoint.reducedSupportι B x = IntersectionGeometry.supportPoint C := IntersectionGeometry.supportPreimage_spec B _ hx
  have hxη : x ≠ η := by
    intro h
    have he : IntersectionGeometry.supportPoint C = IntersectionGeometry.supportPoint B := hxC.symm.trans ((congrArg (Geometric.GenericPoint.reducedSupportι B) h).trans hηB)
    have hBC : C = B := irreducibleSetEquivPoints.injective he
    rw [hBC] at hd
    omega
  have htop (y : S) (hxy : x < y) : y = η := by
    by_contra hy
    let D : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm (Geometric.GenericPoint.reducedSupportι B y)
    have hCD : C < D := by
      have h := irreducibleSetEquivPoints.symm.strictMono (hmap hxy)
      rw [hxC] at h
      simpa only [IntersectionGeometry.supportPoint, OrderIso.symm_apply_apply] using h
    have hDB : D < B := by
      have h := irreducibleSetEquivPoints.symm.strictMono (hmap (point_lt_of_le_of_ne (hyη y) hy))
      rw [hηB] at h
      simpa only [IntersectionGeometry.supportPoint, OrderIso.symm_apply_apply] using h
    have h₁ := Intersection.Supports.codimension_strictAnti X hCD
    have h₂ := Intersection.Supports.codimension_strictAnti X hDB
    omega
  apply le_antisymm
  · apply (Order.coheight_le_coe_iff (n := 1)).mpr
    intro y hy
    rw [htop y hy, hη]
    exact zero_lt_one
  · have h := Order.coheight_add_one_le (point_lt_of_le_of_ne (hyη x) hxη)
    rwa [hη, zero_add] at h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SupportCodimension.Constructions
