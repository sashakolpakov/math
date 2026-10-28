import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport

/-! # Finite Subgroup Commutative -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The chosen native subgroups inherit commutativity from their actual
closed embedding, so no extra group-law premise is needed for CartierDuality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {G : Grp (Over (Spec (.of k)))}
variable (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k G)

instance FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup.inclusion_mono : Mono H.inclusion.hom.hom := by
  have : IsClosedImmersion H.inclusion.hom.hom.left := H.closed
  exact Over.mono_of_mono_left _

instance FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup.group_commutative [IsCommMonObj G.X] : IsCommMonObj H.group.X := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (cancel_mono H.inclusion.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
