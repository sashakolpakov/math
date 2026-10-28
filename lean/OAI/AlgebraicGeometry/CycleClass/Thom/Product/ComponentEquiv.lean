import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct

/-! # Component Equiv -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.ComponentEquiv.Constructions

noncomputable section

/-! The genuine components of a product presentation are in bijection with
pairs of actual components, including empty and mixed-dimensional presentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem component_eq_of_common_point (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C D : irreducibleComponents P.carrier) (x : P.carrier) (hc : x ∈ C.val) (hd : x ∈ D.val) : C = D := by
  let := P.stalk_isDomain x
  apply Subtype.ext
  exact Foundations.Scheme.LocalDomainComponents.irreducibleComponents_eq_of_mem_of_stalkDomain x C.property D.property hc hd

variable (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY))

theorem productComponent_injective : Function.Injective
    (fun CD : irreducibleComponents X.carrier × irreducibleComponents Y.carrier =>
      ComponentProduct.Constructions.productComponent X Y CD.1 CD.2 Z πX πY hprod) := by
  rintro ⟨C, D⟩ ⟨C', D'⟩ h
  change ComponentProduct.Constructions.productComponent X Y C D Z πX πY hprod = ComponentProduct.Constructions.productComponent X Y C' D' Z πX πY hprod at h
  obtain ⟨z, hz⟩ := (ComponentProduct.Constructions.productComponent X Y C D Z πX πY hprod).property.1.nonempty
  have hz' : z ∈ (ComponentProduct.Constructions.productComponent X Y C' D' Z πX πY hprod).val := by rwa [← h]
  rw [ComponentProduct.Constructions.productComponent_range] at hz hz'
  exact Prod.ext (component_eq_of_common_point X C C' (πX.left z) hz.1 hz'.1)
    (component_eq_of_common_point Y D D' (πY.left z) hz.2 hz'.2)

theorem productComponent_surjective : Function.Surjective
    (fun CD : irreducibleComponents X.carrier × irreducibleComponents Y.carrier =>
      ComponentProduct.Constructions.productComponent X Y CD.1 CD.2 Z πX πY hprod) := by
  intro E
  obtain ⟨z, hz⟩ := E.property.1.nonempty
  let C : irreducibleComponents X.carrier :=
    ⟨irreducibleComponent (πX.left z), irreducibleComponent_mem_irreducibleComponents (πX.left z)⟩
  let D : irreducibleComponents Y.carrier :=
    ⟨irreducibleComponent (πY.left z), irreducibleComponent_mem_irreducibleComponents (πY.left z)⟩
  refine ⟨(C, D), component_eq_of_common_point Z _ E z ?_ hz⟩
  rw [ComponentProduct.Constructions.productComponent_range]
  exact ⟨mem_irreducibleComponent, mem_irreducibleComponent⟩

def productComponentEquiv : (irreducibleComponents X.carrier × irreducibleComponents Y.carrier) ≃
    irreducibleComponents Z.carrier :=
  Equiv.ofBijective (fun CD => ComponentProduct.Constructions.productComponent X Y CD.1 CD.2 Z πX πY hprod)
    ⟨productComponent_injective X Y Z πX πY hprod, productComponent_surjective X Y Z πX πY hprod⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.ComponentEquiv.Constructions
