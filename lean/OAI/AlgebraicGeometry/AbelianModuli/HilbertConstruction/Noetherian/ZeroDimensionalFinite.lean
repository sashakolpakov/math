import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace

/-! # Zero Dimensional Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ZeroDimensionalFinite

noncomputable section

/-! A Noetherian T0 space of dimension at most zero is finite. Every
point is then the generic point of an irreducible component, and there
are only finitely many such components. This applies to the underlying
space of a zero-dimensional closed scheme obtained by cuts. -/
open _root_.TopologicalSpace
universe u

theorem genericPoint_of_topologicalKrullDim_nonpos
    {X : Type u} [TopologicalSpace X] (h : topologicalKrullDim X ≤ 0) (x : X) :
    x ∈ genericPoints X := by
  have hm : ∀ Z : IrreducibleCloseds X, IsMax Z := Order.krullDim_nonpos_iff_forall_isMax.mp h
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  change closure {x} ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  intro Y hY hZY
  exact hm Z (show Z ≤ (⟨Y, hY.2, hY.1⟩ : IrreducibleCloseds X) from hZY)

theorem finite_of_noetherian_topologicalKrullDim_nonpos
    (X : Type u) [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    (h : topologicalKrullDim X ≤ 0) : Finite X := by
  have hf : (genericPoints X).Finite := genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  let : Finite (genericPoints X) := hf.to_subtype
  exact Finite.of_injective (fun x : X => (⟨x, genericPoint_of_topologicalKrullDim_nonpos h x⟩ : genericPoints X))
    (fun _ _ hxy => congrArg Subtype.val hxy)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ZeroDimensionalFinite
