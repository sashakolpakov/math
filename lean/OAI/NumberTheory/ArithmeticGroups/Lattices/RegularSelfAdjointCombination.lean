import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Regular Self Adjoint Combination -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSelfAdjointCombination.Construction

noncomputable section

/-! A finite commuting family of self-adjoint operators has a real
linear combination whose kernel is precisely their common kernel. -/

open scoped Classical
open _root_.Module.End

theorem exists_selfAdjoint_combination_common_kernel
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] (T : ι → E →ₗ[ℝ] E) (hT : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise (fun i j => Commute (T i) (T j))) :
    ∃ c : ι → ℝ, (∑ i, c i • T i).ker = ⨅ i, (T i).ker := by
  let P : (ι → ℝ) → Submodule ℝ E := fun χ => ⨅ i, eigenspace (T i) (χ i)
  have hind : iSupIndep P := (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT).independent
  let : Fintype {χ : ι → ℝ // P χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  let J := {χ : ι → ℝ // P χ ≠ ⊥ ∧ χ ≠ 0}
  let : Finite J := Finite.of_injective
    (fun χ : J => (⟨χ.val, χ.property.1⟩ : {χ : ι → ℝ // P χ ≠ ⊥}))
    (fun _ _ h => Subtype.ext (congrArg (fun χ : {χ : ι → ℝ // P χ ≠ ⊥} => χ.val) h))
  let f : J → Module.Dual ℝ (ι → ℝ) := fun χ => ∑ i, χ.val i • LinearMap.proj i
  have hf (χ : J) : ∃ c, f χ c ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp χ.property.2
    refine ⟨Pi.single i 1, ?_⟩
    simpa [f, LinearMap.sum_apply, LinearMap.smul_apply, Pi.single_apply] using hi
  obtain ⟨c, hc⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  have hav (χ : ι → ℝ) (hP : P χ ≠ ⊥) (hχ : χ ≠ 0) : ∑ i, c i * χ i ≠ 0 := by
    simpa only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul, mul_comm] using hc ⟨χ, hP, hχ⟩
  let S : E →ₗ[ℝ] E := ∑ i, c i • T i
  have hSym : S.IsSymmetric := LinearMap.isSymmetric_sum Finset.univ
    (fun i _ => LinearMap.IsSymmetric.smul (by simp) (hT i))
  have heig (χ : ι → ℝ) (y : E) (hy : y ∈ P χ) (i : ι) : T i y = χ i • y :=
    Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy i)
  have heigS (χ : ι → ℝ) (y : E) (hy : y ∈ P χ) : S y = (∑ i, c i * χ i) • y := by
    simp only [S, LinearMap.sum_apply, LinearMap.smul_apply]
    calc
      (∑ i, c i • T i y) = ∑ i, (c i * χ i) • y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [heig χ y hy i, smul_smul]
      _ = _ := Finset.sum_smul.symm
  have htop : (⨆ χ, P χ) = ⊤ := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hcomm
  refine ⟨c, le_antisymm ?_ ?_⟩
  · intro x hx
    change S x = 0 at hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    change T i x = 0
    let F := (innerSL ℝ (T i x)).toLinearMap
    have hker : (⨆ χ, P χ) ≤ F.ker := by
      apply iSup_le
      intro χ y hy
      change inner ℝ (T i x) y = 0
      by_cases hp : P χ = ⊥
      · have hy0 : y = 0 := by simpa only [hp, Submodule.mem_bot] using hy
        rw [hy0, inner_zero_right]
      by_cases hz : χ = 0
      · have hyi := heig χ y hy i
        rw [hz, Pi.zero_apply, zero_smul] at hyi
        rw [hT i x y, hyi, inner_zero_right]
      have hs := hSym x y
      rw [hx, heigS χ y hy, inner_zero_left, real_inner_smul_right] at hs
      have hxy : inner ℝ x y = 0 := (mul_eq_zero.mp hs.symm).resolve_left (hav χ hp hz)
      rw [hT i x y, heig χ y hy i, real_inner_smul_right, hxy, mul_zero]
    rw [htop] at hker
    have hz : inner ℝ (T i x) (T i x) = 0 := hker (show T i x ∈ (⊤ : Submodule ℝ E) from trivial)
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp hz
  · intro x hx
    change (∑ i, c i • T i) x = 0
    have hi (i : ι) : T i x = 0 := (Submodule.mem_iInf _).mp hx i
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hi, smul_zero, Finset.sum_const_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSelfAdjointCombination.Construction
