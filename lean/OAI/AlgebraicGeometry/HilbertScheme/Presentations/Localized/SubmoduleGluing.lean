import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Submodule Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.SubmoduleGluing

noncomputable section

/-!
Gluing submodules on a finite family of principal localizations by clearing
overlap denominators. This constructs the global submodule and proves that
its restrictions are exactly the supplied local submodules.
-/

open LocalizedModule

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {κ : Type w} [Fintype κ] (r : κ → R)
variable {A : κ → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, IsLocalization.Away (r i) (A i)]
variable {L : κ → Type v} [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)]
variable [∀ i, Module (A i) (L i)] [∀ i, IsScalarTower R (A i) (L i)]
variable (f : ∀ i, M →ₗ[R] L i) [∀ i, IsLocalizedModule.Away (r i) (f i)]
variable (N : ∀ i, Submodule (A i) (L i))

def localizedSubmoduleIntersection : Submodule R M :=
  ⨅ i, ((N i).restrictScalars R).comap (f i)

def LocalizedSubmoduleClearing : Prop :=
  ∀ i j m, f i m ∈ N i → ∃ k : ℕ, f j ((r i) ^ k • m) ∈ N j

omit [∀ i, IsLocalization.Away (r i) (A i)] [∀ i, IsLocalizedModule.Away (r i) (f i)] in
theorem localizedSubmodule_clear_all (hN : LocalizedSubmoduleClearing r f N)
    (i : κ) (m : M) (hm : f i m ∈ N i) :
    ∃ k : ℕ, (r i) ^ k • m ∈ localizedSubmoduleIntersection f N := by
  classical
  choose k hk using fun j => hN i j m hm
  let d := ∑ j, k j
  refine ⟨d, ?_⟩
  apply (Submodule.mem_iInf _).mpr
  intro j
  change f j ((r i) ^ d • m) ∈ N j
  have hj : k j ≤ d := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have he : f j ((r i) ^ d • m) = (r i) ^ (d - k j) • f j ((r i) ^ k j • m) := by
    rw [← map_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hj]
  rw [he]
  exact ((N j).restrictScalars R).smul_mem _ (hk j)

/-- Pairwise denominator clearing suffices to glue a finite family of local
submodules. No finite generation or noetherian hypothesis is needed. -/
theorem localizedSubmoduleIntersection_localized (hN : LocalizedSubmoduleClearing r f N) (i : κ) :
    (localizedSubmoduleIntersection f N).localized' (A i) (Submonoid.powers (r i)) (f i) = N i := by
  apply le_antisymm
  · rw [Submodule.localized'_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact (Submodule.mem_iInf _).mp hm i
  · intro y hy
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers (r i)) (f i) y
    have hm : f i m ∈ N i := by
      rw [← IsLocalizedModule.mk'_cancel' _ _ s, Submonoid.smul_def]
      exact ((N i).restrictScalars R).smul_mem _ hy
    obtain ⟨k, hk⟩ := localizedSubmodule_clear_all r f N hN i m hm
    let t : Submonoid.powers (r i) := ⟨(r i) ^ k, ⟨k, rfl⟩⟩
    refine ⟨(r i) ^ k • m, hk, t * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left _ m t s

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.SubmoduleGluing
