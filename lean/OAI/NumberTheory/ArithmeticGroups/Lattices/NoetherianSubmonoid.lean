import Mathlib

/-! # Noetherian Submonoid -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NoetherianSubmonoid.Construction

noncomputable section

/-! A closed submonoid of a Noetherian group with continuous translations
is a subgroup. This applies to algebraic matrix groups with their Zariski
topology, which need only separate continuity of multiplication. -/

open scoped Classical
open Set _root_.TopologicalSpace

theorem closed_noetherian_submonoid_inv_mem
    {H : Type*} [Group H] [TopologicalSpace H] [SeparatelyContinuousMul H]
    [NoetherianSpace H] (M : Submonoid H) (hM : IsClosed (M : Set H))
    {x : H} (hx : x ∈ M) : x⁻¹ ∈ M := by
  let F : ℕ → Closeds H := fun n =>
    ⟨(fun y : H => x ^ n * y) '' (M : Set H),
      (Homeomorph.mulLeft (x ^ n)).isClosedMap _ hM⟩
  obtain ⟨Z, hZ, hmin⟩ := WellFoundedLT.exists_minimal
    (inferInstance : WellFoundedLT (Closeds H)) (Set.range F) ⟨F 0, mem_range_self 0⟩
  obtain ⟨n, rfl⟩ := hZ
  have hle : F (n + 1) ≤ F n := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨x * y, M.mul_mem hx hy, ?_⟩
    simp only [pow_succ, mul_assoc]
  have hback : F n ≤ F (n + 1) := hmin (mem_range_self (n + 1)) hle
  have hxn : x ^ n ∈ F n := ⟨1, M.one_mem, mul_one _⟩
  obtain ⟨y, hy, he⟩ := hback hxn
  have hxy : x * y = 1 := by
    apply mul_left_cancel (a := x ^ n)
    simpa only [pow_succ, mul_assoc, mul_one] using he
  have heq : y = x⁻¹ := by
    calc
      y = x⁻¹ * (x * y) := by simp
      _ = x⁻¹ := by rw [hxy, mul_one]
  exact heq ▸ hy

def closedNoetherianSubgroup
    {H : Type*} [Group H] [TopologicalSpace H] [SeparatelyContinuousMul H]
    [NoetherianSpace H] (M : Submonoid H) (hM : IsClosed (M : Set H)) : Subgroup H where
  toSubmonoid := M
  inv_mem' := fun hx => closed_noetherian_submonoid_inv_mem M hM hx

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NoetherianSubmonoid.Construction
