import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.Noetherian.Basic

/-! # Module Generators -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules

noncomputable section

/-!
Homogeneous generators and kernels for graded modules. These give the
finite graded presentations needed for the projective Hilbert-family
argument, with no extra representability assumptions.
-/

open DirectSum

universe u v w t

variable {A : Type u} [Semiring A] {M : Type v} [AddCommMonoid M] [Module A M]
variable {ι : Type w} [DecidableEq ι] {σ : Type t} [SetLike σ M] [AddSubmonoidClass σ M]
variable (ℳ : ι → σ) [Decomposition ℳ]

theorem span_homogeneous_members (P : Submodule A M) (hP : P.IsHomogeneous ℳ) :
    Submodule.span A {m : M | m ∈ P ∧ ∃ d, m ∈ ℳ d} = P := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hm => hm.1)
  · intro m hm
    classical
    rw [← DirectSum.sum_support_decompose ℳ m]
    apply Submodule.sum_mem
    intro d _
    exact Submodule.subset_span ⟨hP d hm, d, (DirectSum.decompose ℳ m d).property⟩

theorem exists_finite_homogeneous_generators (P : Submodule A M) (hP : P.IsHomogeneous ℳ)
    (hfg : P.FG) :
    ∃ s : Finset M, Submodule.span A (s : Set M) = P ∧ ∀ m ∈ s, ∃ d, m ∈ ℳ d := by
  have hs := span_homogeneous_members ℳ P hP
  have hfg' : (Submodule.span A {m : M | m ∈ P ∧ ∃ d, m ∈ ℳ d}).FG := hs.symm ▸ hfg
  obtain ⟨s, hsub, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg'
  exact ⟨s, hspan.symm.trans hs, fun m hm => (hsub hm).2⟩

theorem noetherian_homogeneous_generators [IsNoetherian A M]
    (P : Submodule A M) (hP : P.IsHomogeneous ℳ) :
    ∃ s : Finset M, Submodule.span A (s : Set M) = P ∧ ∀ m ∈ s, ∃ d, m ∈ ℳ d :=
  exists_finite_homogeneous_generators ℳ P hP (IsNoetherian.noetherian P)

variable {N : Type*} [AddCommMonoid N] {τ : Type*} [SetLike τ N] [AddSubmonoidClass τ N]
variable (𝒩 : ι → τ) [Decomposition 𝒩]

omit [Semiring A] [Module A M] in
theorem map_homogeneous_component (f : M →+ N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d)
    (d : ι) (m : M) :
    f (DirectSum.decompose ℳ m d).val = (DirectSum.decompose 𝒩 (f m) d).val := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous m =>
    rename_i i
    by_cases h : i = d
    · subst i
      rw [DirectSum.decompose_of_mem_same ℳ m.property,
        DirectSum.decompose_of_mem_same 𝒩 (hf d m.val m.property)]
    · rw [DirectSum.decompose_of_mem_ne ℳ m.property h,
        DirectSum.decompose_of_mem_ne 𝒩 (hf i m.val m.property) h, map_zero]
  | add x y hx hy =>
    rw [DirectSum.decompose_add, map_add, DirectSum.decompose_add]
    change f ((DirectSum.decompose ℳ x d).val + (DirectSum.decompose ℳ y d).val) =
      (DirectSum.decompose 𝒩 (f x) d).val + (DirectSum.decompose 𝒩 (f y) d).val
    rw [map_add, hx, hy]

variable [Module A N]

theorem homogeneous_kernel (f : M →ₗ[A] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) :
    f.ker.IsHomogeneous ℳ := by
  intro d m hm
  change f (DirectSum.decompose ℳ m d).val = 0
  refine (map_homogeneous_component ℳ 𝒩 f.toAddMonoidHom hf d m).trans ?_
  change (DirectSum.decompose 𝒩 (f m) d).val = 0
  change f m = 0 at hm
  rw [hm, DirectSum.decompose_zero]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules
