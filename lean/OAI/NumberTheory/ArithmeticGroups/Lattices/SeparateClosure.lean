import Mathlib

/-! # Separate Closure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SeparateClosure.Construction

noncomputable section

section

/-! Subgroup closure with separate continuity, suitable for geometric
Zariski topologies. -/

open scoped Classical commutatorElement
open Set _root_.Topology

variable {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H]

def separateSubgroupClosure (K : Subgroup H) : Subgroup H where
  carrier := _root_.closure (K : Set H)
  one_mem' := subset_closure K.one_mem
  mul_mem' := by
    intro x y hx hy
    apply closure_minimal (t := {a : H | a * y ∈ _root_.closure (K : Set H)})
      _ (isClosed_closure.preimage (continuous_mul_const y)) hx
    intro a ha
    exact map_mem_closure (continuous_const_mul a) hy
      (fun z hz => K.mul_mem ha hz)
  inv_mem' := by
    intro x hx
    exact map_mem_closure continuous_inv hx (fun z hz => K.inv_mem hz)

theorem separateSubgroupClosure_mono {K L : Subgroup H} (h : K ≤ L) :
    separateSubgroupClosure K ≤ separateSubgroupClosure L := closure_mono h

theorem separateSubgroupClosure_normal (K : Subgroup H) [K.Normal] :
    (separateSubgroupClosure K).Normal := by
  constructor
  intro x hx g
  apply map_mem_closure
    ((continuous_mul_const g⁻¹).comp (continuous_const_mul g)) hx
  intro y hy
  exact Subgroup.Normal.conj_mem inferInstance y hy g

theorem commutator_separateClosure_le
    (hleft : ∀ y : H, Continuous (fun x : H => ⁅x, y⁆))
    (hright : ∀ x : H, Continuous (fun y : H => ⁅x, y⁆)) (K L : Subgroup H) :
    ⁅separateSubgroupClosure K, separateSubgroupClosure L⁆ ≤
      separateSubgroupClosure ⁅K, L⁆ := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  apply closure_minimal (t := {a : H | ⁅a, y⁆ ∈ _root_.closure ((⁅K, L⁆ : Subgroup H) : Set H)})
    _ (isClosed_closure.preimage (hleft y)) hx
  intro a ha
  exact map_mem_closure (hright a) hy
    (fun z hz => Subgroup.commutator_mem_commutator ha hz)

end

/-! Solvability is preserved by closure when commutator maps are separately
continuous. This formulation applies to geometric Zariski topologies. -/

open scoped Classical commutatorElement
open Set

def iteratedSubgroupDerived {H : Type*} [Group H] (K : Subgroup H) : ℕ → Subgroup H
  | 0 => K
  | n + 1 => ⁅iteratedSubgroupDerived K n, iteratedSubgroupDerived K n⁆

theorem map_derivedSeries_subtype {H : Type*} [Group H] (K : Subgroup H) (n : ℕ) :
    (derivedSeries K n).map K.subtype = Construction.iteratedSubgroupDerived K n := by
  induction n with
  | zero =>
    change (⊤ : Subgroup K).map K.subtype = K
    rw [← MonoidHom.range_eq_map, K.range_subtype]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, ih]
    rfl

theorem solvable_iff_iteratedSubgroupDerived_eq_bot {H : Type*} [Group H] (K : Subgroup H) :
    Group.IsSolvable K ↔ ∃ n, Construction.iteratedSubgroupDerived K n = ⊥ := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.solvable
    refine ⟨n, ?_⟩
    rw [← map_derivedSeries_subtype, hn, Subgroup.map_bot]
  · rintro ⟨n, hn⟩
    constructor
    refine ⟨n, ?_⟩
    apply (Subgroup.map_injective K.subtype_injective)
    rw [map_derivedSeries_subtype, hn, Subgroup.map_bot]

theorem iteratedDerived_separateClosure_le
    {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H]
    (hleft : ∀ y : H, Continuous (fun x : H => ⁅x, y⁆))
    (hright : ∀ x : H, Continuous (fun y : H => ⁅x, y⁆)) (K : Subgroup H) (n : ℕ) :
    Construction.iteratedSubgroupDerived (separateSubgroupClosure K) n ≤
      separateSubgroupClosure (Construction.iteratedSubgroupDerived K n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (Subgroup.commutator_mono ih ih).trans
      (commutator_separateClosure_le hleft hright _ _)

theorem separateClosure_solvable
    {H : Type*} [Group H] [TopologicalSpace H] [T1Space H]
    [SeparatelyContinuousMul H] [ContinuousInv H]
    (hleft : ∀ y : H, Continuous (fun x : H => ⁅x, y⁆))
    (hright : ∀ x : H, Continuous (fun y : H => ⁅x, y⁆))
    (K : Subgroup H) [hK : Group.IsSolvable K] :
    Group.IsSolvable (separateSubgroupClosure K) := by
  obtain ⟨n, hn⟩ := (solvable_iff_iteratedSubgroupDerived_eq_bot K).mp hK
  apply (solvable_iff_iteratedSubgroupDerived_eq_bot (separateSubgroupClosure K)).mpr
  refine ⟨n, le_antisymm ?_ bot_le⟩
  have h := iteratedDerived_separateClosure_le hleft hright K n
  rw [hn] at h
  exact h.trans (show separateSubgroupClosure (⊥ : Subgroup H) ≤ ⊥ from by
    intro x hx
    change x ∈ _root_.closure ({1} : Set H) at hx
    rw [closure_singleton] at hx
    exact mem_singleton_iff.mp hx)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SeparateClosure.Construction
