import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.Topology.LocallyConstant.Basic

/-! # Specialization Constancy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.SpecializationConstancy

noncomputable section

/-! A function invariant under specialization on a Noetherian quasi-sober space is locally constant. Each inverse image is a finite union of irreducible components. -/
open _root_.TopologicalSpace
universe u v

theorem noetherian_isLocallyConstant_of_specialization
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    {Y : Type v} (f : X → Y) (h : ∀ x y, x ⤳ y → f x = f y) : IsLocallyConstant f := by
  have : Finite (irreducibleComponents X) := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let g : irreducibleComponents X → X := fun C => (genericPoints.ofComponent C).val
  have hc (C : irreducibleComponents X) (x : X) (hx : x ∈ C.val) : f (g C) = f x :=
    h _ _ ((genericPoints.isGenericPoint_ofComponent C).specializes hx)
  have hclosed (V : Set Y) : IsClosed (f ⁻¹' V) := by
    let I := {C : irreducibleComponents X // f (g C) ∈ V}
    have he : f ⁻¹' V = ⋃ C : I, C.val.val := by
      ext x
      constructor
      · intro hx
        let C : irreducibleComponents X := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
        have hxC : x ∈ C.val := mem_irreducibleComponent
        exact Set.mem_iUnion.mpr ⟨⟨C, (hc C x hxC).symm ▸ hx⟩, hxC⟩
      · intro hx
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
        change f x ∈ V
        exact (hc C.val x hxC) ▸ C.property
    rw [he]
    exact isClosed_iUnion_of_finite (fun C : I => isClosed_of_mem_irreducibleComponents C.val.val C.val.property)
  intro V
  simpa only [Set.preimage_compl, compl_compl] using (hclosed Vᶜ).isOpen_compl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.SpecializationConstancy
