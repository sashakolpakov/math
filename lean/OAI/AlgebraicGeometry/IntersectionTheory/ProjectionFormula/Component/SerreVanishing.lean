import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GeometricEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedGeometricComponents

/-! # Serre Vanishing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.SerreVanishing

noncomputable section

/-! Every irreducible intersection component gives an isolated
native stalk pairing. Components of excess dimension have zero
native Tor Euler coefficient by Serre vanishing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem maximal (Z : Scheme.{0}) (S : Closeds Z) (c : irreducibleComponents S)
    (D : IrreducibleCloseds Z) (hD : (D : Set Z) ⊆ S)
    (hcD : CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z S c ≤ D) : D = CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z S c := by
  let : IrreducibleSpace D := isIrreducible_iff_irreducibleSpace.mp D.isIrreducible
  let j : D → S := fun y => ⟨y, hD y.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hi : IsIrreducible (j '' (Set.univ : Set D)) :=
    (IrreducibleSpace.isIrreducible_univ D).image j hj.continuousOn
  have hc : c.val ⊆ j '' (Set.univ : Set D) := by
    intro y hy
    have hyD : y.val ∈ (D : Set Z) := hcD ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, hyD⟩, Set.mem_univ _, Subtype.ext rfl⟩
  have hback := c.property.2 hi hc
  apply le_antisymm
  · intro y hy
    exact ⟨⟨y, hD hy⟩, hback ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩, rfl⟩
  · exact hcD

theorem isolated (Z : Scheme.{0}) [NoetherianSpace Z]
    (A B C : IrreducibleCloseds Z)
    (hC : C ∈ Finite.ClosedComponents.components Z (IsolatedGeometricComponents.intersection Z A B))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set Z)) (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set Z)) :
    Module.support (Z.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA) ∩
      Module.support (Z.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB) ⊆
        {IsLocalRing.closedPoint (Z.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C))} := by
  intro p hp
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C
  let z := Z.fromSpecStalk x p
  let D : IrreducibleCloseds Z := irreducibleSetEquivPoints.symm z
  let S := IsolatedGeometricComponents.intersection Z A B
  have hzA : z ∈ (A : Set Z) := Local.SupportSpectrum.image_mem_support Z A x hxA p hp.1
  have hzB : z ∈ (B : Set Z) := Local.SupportSpectrum.image_mem_support Z B x hxB p hp.2
  have hD : (D : Set Z) ⊆ S :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨hzA, hzB⟩) S.isClosed
  have hz : z ⤳ x := by
    have hr : z ∈ Set.range (Z.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hCD : C ≤ D := by
    apply (Supports.supportPoint_mem_iff_subset ⟨D, D.isClosed⟩ C).mp
    exact hz.mem_closed isClosed_closure (subset_closure (Set.mem_singleton z))
  obtain ⟨c, hc⟩ := (Finite.ClosedComponents.mem_iff Z S C).mp hC
  have he : D = C := (maximal Z S c D hD (hc.symm ▸ hCD)).trans hc
  have hzx : z = x := (irreducibleSetEquivPoints.apply_symm_apply z).symm.trans
    (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he)
  apply Set.mem_singleton_iff.mpr
  apply (Z.fromSpecStalk x).isEmbedding.injective
  exact hzx.trans Scheme.fromSpecStalk_closedPoint.symm

theorem zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A B C : IrreducibleCloseds X.carrier)
    (hC : C ∈ Finite.ClosedComponents.components X.carrier
      (IsolatedGeometricComponents.intersection X.carrier A B))
    (hd : X.supportCodimension C < X.supportCodimension A + X.supportCodimension B) :
    TotalTorCoefficient.coefficient X.carrier A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) m = 0 := by
  have hsubset := Finite.ClosedComponents.subset X.carrier
    (IsolatedGeometricComponents.intersection X.carrier A B) C hC
  have hx := hsubset (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  change CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier) ∧ CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier) at hx
  rw [TotalTorCoefficient.coefficient, dite_eq_left hx]
  exact Smooth.GeometricEuler.supports_at X m A B C (CycleClass.Thom.IntersectionGeometry.supportPoint C) rfl hx.1 hx.2 hd
    (isolated X.carrier A B C hC hx.1 hx.2)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.SerreVanishing
