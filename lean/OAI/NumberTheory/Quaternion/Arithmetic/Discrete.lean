import OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanProjection
import OAI.NumberTheory.Quaternion.Arithmetic.OpenSubgroupDiscrete

/-! # Discrete -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Discrete

noncomputable section

/-! S-integral rational points form a discrete subgroup of the
product of the places in S when all archimedean places are included. -/

open scoped Classical _root_.NumberField
open _root_.NumberField Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem sArithmeticLocalSubgroup_discrete (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ v : InfinitePlace F, Sum.inl v ∈ S) : DiscreteTopology (Adelic.sArithmeticLocalSubgroup G S) := by
  let Δ := Adelic.sArithmeticLocalSubgroup G S
  let U := (ArchimedeanProjection.integralLocalProductSubgroup G S).subgroupOf Δ
  let Λ := (G.latticeStabilizer (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n)).map (G.diagonal Set.univ)
  let : DiscreteTopology Λ := ArithmeticGroups.Lattices.Discrete.Construction.full_diagonal_stabilizer_discrete G (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n)
  let f : U → Λ := fun z => ⟨ArchimedeanProjection.localProductArchimedeanMap G S harch z.val.val,
    ArchimedeanProjection.integral_arithmetic_archimedean_mem G S harch z.val z.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : U => z.val.val) := continuous_subtype_val.comp continuous_subtype_val
    exact (ArchimedeanProjection.localProductArchimedeanMap_continuous G S harch).comp hc
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply ArchimedeanProjection.arithmetic_archimedeanProjection_injective G S harch
    exact congrArg Subtype.val he
  let : DiscreteTopology U := DiscreteTopology.of_continuous_injective hf hi
  have ho : IsOpen (U : Set Δ) :=
    (ArchimedeanProjection.integralLocalProductSubgroup_isOpen G S).preimage continuous_subtype_val
  exact OpenSubgroupDiscrete.discreteTopology_of_open_subgroup U ho

end

end OAI.NumberTheory.Quaternion.Arithmetic.Discrete
