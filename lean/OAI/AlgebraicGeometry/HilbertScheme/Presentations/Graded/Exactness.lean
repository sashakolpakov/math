import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators
import Mathlib.Algebra.Exact.Basic

/-! # Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness.GradedModules

noncomputable section

/-! Exact sequences of graded modules are exact in every homogeneous degree. -/

open DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {δ : Type v} [DecidableEq δ]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type t} [AddCommGroup N] [Module R N]
variable (ℳ : δ → Submodule R M) (𝒩 : δ → Submodule R N)

def degreeMap (f : M →ₗ[R] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : δ) :
    ℳ d →ₗ[R] 𝒩 d :=
  (f.comp (ℳ d).subtype).codRestrict (𝒩 d) (fun x => hf d x.val x.property)

variable [Decomposition ℳ] [Decomposition 𝒩]

theorem homogeneous_preimage (f : M →ₗ[R] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d)
    (d : δ) (n : N) (hn : n ∈ 𝒩 d) (m : M) (hm : f m = n) :
    f (decompose ℳ m d).val = n := by
  refine (ModuleGenerators.GradedModules.map_homogeneous_component ℳ 𝒩 f.toAddMonoidHom hf d m).trans ?_
  change (decompose 𝒩 (f m) d).val = n
  rw [hm]
  exact decompose_of_mem_same 𝒩 hn

theorem degreeMap_surjective (f : M →ₗ[R] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d)
    (hs : Function.Surjective f) (d : δ) : Function.Surjective (degreeMap ℳ 𝒩 f hf d) := by
  intro n
  obtain ⟨m, hm⟩ := hs n.val
  refine ⟨decompose ℳ m d, Subtype.ext ?_⟩
  exact homogeneous_preimage ℳ 𝒩 f hf d n.val n.property m hm

variable {P : Type*} [AddCommGroup P] [Module R P]
variable (ℙ : δ → Submodule R P)

theorem degreeMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hg : ∀ d n, n ∈ 𝒩 d → g n ∈ ℙ d)
    (hex : Function.Exact f g) (d : δ) :
    Function.Exact (degreeMap ℳ 𝒩 f hf d) (degreeMap 𝒩 ℙ g hg d) := by
  intro n
  constructor
  · intro hn
    have hn' : g n.val = 0 := congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := (hex n.val).mp hn'
    refine ⟨decompose ℳ m d, Subtype.ext ?_⟩
    exact homogeneous_preimage ℳ 𝒩 f hf d n.val n.property m hm
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    exact (hex n.val).mpr ⟨m.val, congrArg Subtype.val hm⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness.GradedModules
