import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Kernel Discrete -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelDiscrete.Construction

noncomputable section

/-! Finite-kernel homomorphisms pull discrete subgroups back to discrete
subgroups of Hausdorff topological groups. -/

open scoped Classical

theorem discrete_of_discrete_target_finite_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) [Finite f.ker] (hf : Continuous f) : DiscreteTopology G := by
  let : DiscreteTopology f.ker := inferInstance
  have hker : IsOpen (f.ker : Set G) :=
    (isOpen_discrete ({1} : Set H)).preimage hf
  apply discreteTopology_of_isOpen_singleton_one
  have h := hker.isOpenEmbedding_subtypeVal.isOpenMap ({1} : Set f.ker) (isOpen_discrete _)
  simpa only [Set.image_singleton, OneMemClass.coe_one] using h

theorem discrete_comap_of_finite_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    [Group H] [TopologicalSpace H] (f : G →* H) [Finite f.ker]
    (hf : Continuous f) (Γ : Subgroup H) [DiscreteTopology Γ] :
    DiscreteTopology (Γ.comap f) := by
  let r : Γ.comap f →* Γ :=
    (f.comp (Γ.comap f).subtype).codRestrict Γ (fun x => x.property)
  have hr : Continuous r := (hf.comp continuous_subtype_val).subtype_mk _
  let j : r.ker → f.ker := fun x => ⟨x.val.val, congrArg (fun y : Γ => y.val) x.property⟩
  let : Finite r.ker := Finite.of_injective j (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) h)
  exact discrete_of_discrete_target_finite_kernel r hr

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelDiscrete.Construction
