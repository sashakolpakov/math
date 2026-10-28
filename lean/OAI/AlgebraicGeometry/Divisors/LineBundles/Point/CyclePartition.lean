import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow

/-! # Cycle Partition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CyclePartition.BundleCycles

noncomputable section

section

/-! A finite partition into injectively parametrized subsets decomposes
actual point cycles by restriction and extension by zero. -/

theorem pointCycle_map_comap_apply_of_mem {X U : Type*} (i : U → X) (hi : Function.Injective i)
    (z : X →₀ ℚ) (x : X) (hx : x ∈ Set.range i) :
    Finsupp.mapDomain i (Finsupp.comapDomain i z hi.injOn) x = z x := by
  obtain ⟨u, rfl⟩ := hx
  rw [Finsupp.mapDomain_apply_of_injective hi, Finsupp.comapDomain_apply]

theorem pointCycle_finitePartition {X ι : Type*} [Fintype ι] (U : ι → Type*)
    (i : ∀ k, U k → X) (hi : ∀ k, Function.Injective (i k))
    (hcover : ∀ x : X, ∃! k, x ∈ Set.range (i k)) (z : X →₀ ℚ) :
    ∑ k, Finsupp.mapDomain (i k) (Finsupp.comapDomain (i k) z (hi k).injOn) = z := by
  classical
  ext x
  simp only [Finsupp.finsetSum_apply]
  obtain ⟨k, hk, huniq⟩ := hcover x
  rw [Finset.sum_eq_single k]
  · exact pointCycle_map_comap_apply_of_mem (i k) (hi k) z x hk
  · intro b _ hbk
    exact Finsupp.mapDomain_of_notMem_range _ _ (fun hb => hbk (huniq b hb))
  · simp

end

/-! Finite point-cycle decomposition only needs a partition on the
finite support of the cycle itself. -/

theorem pointCycle_map_comap_apply_zero {X U : Type*} (i : U → X) (hi : Function.Injective i)
    (z : X →₀ ℚ) (x : X) (hx : z x = 0) :
    Finsupp.mapDomain i (Finsupp.comapDomain i z hi.injOn) x = 0 := by
  by_cases h : x ∈ Set.range i
  · exact (pointCycle_map_comap_apply_of_mem i hi z x h).trans hx
  · exact Finsupp.mapDomain_of_notMem_range _ _ h

theorem pointCycle_finitePartition_of_support {X ι : Type*} [Fintype ι] (U : ι → Type*)
    (i : ∀ k, U k → X) (hi : ∀ k, Function.Injective (i k)) (z : X →₀ ℚ)
    (hcover : ∀ x ∈ z.support, ∃! k, x ∈ Set.range (i k)) :
    ∑ k, Finsupp.mapDomain (i k) (Finsupp.comapDomain (i k) z (hi k).injOn) = z := by
  classical
  ext x
  simp only [Finsupp.finsetSum_apply]
  by_cases hx : x ∈ z.support
  · obtain ⟨k, hk, huniq⟩ := hcover x hx
    rw [Finset.sum_eq_single k]
    · exact pointCycle_map_comap_apply_of_mem (i k) (hi k) z x hk
    · intro b _ hbk
      exact Finsupp.mapDomain_of_notMem_range _ _ (fun hb => hbk (huniq b hb))
    · simp
  · have hz : z x = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hx
    rw [hz]
    exact Finset.sum_eq_zero (fun k _ => pointCycle_map_comap_apply_zero (i k) (hi k) z x hz)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CyclePartition.BundleCycles
