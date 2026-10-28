import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators

/-! # Shift Equiv -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ShiftEquiv.GradedModules

noncomputable section

/-! A homogeneous automorphism induces equivalences between shifted degree pieces. -/

open DirectSum

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]

theorem map_shifted_component (f : M →ₗ[R] M) (e : ℤ)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ ℳ (d + e)) (d : ℤ) (m : M) :
    f (decompose ℳ m d).val = (decompose ℳ (f m) (d + e)).val := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous m =>
    rename_i i
    by_cases hi : i = d
    · subst i
      rw [decompose_of_mem_same ℳ m.property, decompose_of_mem_same ℳ (hf d m.val m.property)]
    · have hie : i + e ≠ d + e := fun h => hi (add_right_cancel h)
      rw [decompose_of_mem_ne ℳ m.property hi,
        decompose_of_mem_ne ℳ (hf i m.val m.property) hie, map_zero]
  | add x y hx hy =>
    rw [decompose_add, map_add, decompose_add]
    change f ((decompose ℳ x d).val + (decompose ℳ y d).val) =
      (decompose ℳ (f x) (d + e)).val + (decompose ℳ (f y) (d + e)).val
    rw [map_add, hx, hy]

def shiftedDegreeMap (f : M →ₗ[R] M) (e : ℤ)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ ℳ (d + e)) (d : ℤ) : ℳ d →ₗ[R] ℳ (d + e) :=
  (f.comp (ℳ d).subtype).codRestrict (ℳ (d + e)) (fun m => hf d m.val m.property)

def gradedShiftEquiv (f : M ≃ₗ[R] M) (e : ℤ)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ ℳ (d + e)) (d : ℤ) : ℳ d ≃ₗ[R] ℳ (d + e) :=
  LinearEquiv.ofBijective (shiftedDegreeMap ℳ f.toLinearMap e hf d) ⟨by
    intro x y h
    exact Subtype.ext (f.injective (congrArg Subtype.val h)), by
    intro y
    refine ⟨decompose ℳ (f.symm y.val) d, Subtype.ext ?_⟩
    refine (map_shifted_component ℳ f.toLinearMap e hf d (f.symm y.val)).trans ?_
    change (decompose ℳ (f (f.symm y.val)) (d + e)).val = y.val
    rw [LinearEquiv.apply_symm_apply, decompose_of_mem_same ℳ y.property]⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ShiftEquiv.GradedModules
