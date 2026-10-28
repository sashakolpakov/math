import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LatticeLevels
import Mathlib.NumberTheory.NumberField.Basic

/-! # Standard Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StandardLattice.CM

noncomputable section

/-! Compare an actual full integral lattice in E³ with O_E³. The common
positive denominators are constructed from finite generation and fullness. -/

open scoped Classical
open _root_.NumberField

variable (E : Type*) [Field E] [NumberField E]

def coordinateInclusion : (Fin 3 → RingOfIntegers E) →ₗ[ℤ] (Fin 3 → E) where
  toFun x i := x i
  map_add' x y := by ext i; exact map_add (algebraMap (RingOfIntegers E) E) _ _
  map_smul' a x := by ext i; exact map_zsmul (algebraMap (RingOfIntegers E) E) a (x i)

def standardLattice : Submodule ℤ (Fin 3 → E) := (coordinateInclusion E).range

theorem standardLattice_fg : (standardLattice E).FG := by
  simpa only [Submodule.map_top, standardLattice] using
    (Module.Finite.fg_top (R := ℤ) (M := Fin 3 → RingOfIntegers E)).map (coordinateInclusion E)

omit [NumberField E] in
theorem single_integer_mem (i : Fin 3) (x : RingOfIntegers E) :
    Pi.single i (x : E) ∈ standardLattice E := by
  refine ⟨Pi.single i x, ?_⟩
  ext j
  by_cases h : i = j
  · subst j; simp [coordinateInclusion]
  · simp [coordinateInclusion, Pi.single_eq_of_ne (Ne.symm h)]

theorem standardLattice_full :
    Submodule.span ℚ (standardLattice E : Set (Fin 3 → E)) = ⊤ := by
  let S := Submodule.span ℚ (standardLattice E : Set (Fin 3 → E))
  have hsingle (i : Fin 3) (x : E) : Pi.single i x ∈ S := by
    have hspan : Submodule.span ℚ (Set.range (integralBasis E)) ≤
        S.comap (LinearMap.single ℚ (fun _ : Fin 3 => E) i) := by
      apply Submodule.span_le.mpr
      rintro y ⟨j, rfl⟩
      change Pi.single i (integralBasis E j) ∈ S
      rw [integralBasis_apply]
      exact Submodule.subset_span (single_integer_mem E i (RingOfIntegers.basis E j))
    rw [(integralBasis E).span_eq] at hspan
    exact hspan (Submodule.mem_top : x ∈ (⊤ : Submodule ℚ E))
  apply top_le_iff.mp
  intro x _
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem S (fun i _ => hsingle i (x i))

/-- Both lattice inclusions hold after multiplication by positive rational
integers, so only finitely many rational primes can affect local coordinates. -/
theorem integer_bounds (Λ : Submodule ℤ (Fin 3 → E)) (hfg : Λ.FG)
    (hfull : Submodule.span ℚ (Λ : Set (Fin 3 → E)) = ⊤) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      (∀ x ∈ standardLattice E, m • x ∈ Λ) ∧
      (∀ x ∈ Λ, n • x ∈ standardLattice E) := by
  obtain ⟨m, hm, hml⟩ := LatticeLevels.CM.exists_uniform_multiple
    (standardLattice E) Λ (standardLattice_fg E) hfull
  obtain ⟨n, hn, hnl⟩ := LatticeLevels.CM.exists_uniform_multiple
    Λ (standardLattice E) hfg (standardLattice_full E)
  exact ⟨m, n, hm, hn, hml, hnl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.StandardLattice.CM
