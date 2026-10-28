import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators
import Mathlib.LinearAlgebra.Span.Basic

/-! # Graded Cyclic Submodule -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicSubmodule

noncomputable section

/-! Homogeneous cyclic submodules and their annihilator ideals. -/

open DirectSum
universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

theorem homogeneous_smul_component {m : M} {e : ℤ} (hm : m ∈ ℳ e)
    (a : A) (d : ℤ) :
    (decompose ℳ (a • m) d).val = (decompose 𝒜 a (d - e)).val • m := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    rename_i i
    have ham := SetLike.GradedSMul.smul_mem a.property hm
    by_cases h : i + e = d
    · have h' : i = d - e := by omega
      rw [decompose_of_mem_same ℳ (h ▸ ham), decompose_of_mem_same 𝒜 (h' ▸ a.property)]
    · rw [decompose_of_mem_ne ℳ ham h,
        decompose_of_mem_ne 𝒜 a.property (by omega), zero_smul]
  | add a b ha hb =>
    rw [add_smul, decompose_add, decompose_add]
    change (decompose ℳ (a • m) d).val + (decompose ℳ (b • m) d).val =
      ((decompose 𝒜 a (d - e)).val + (decompose 𝒜 b (d - e)).val) • m
    rw [add_smul, ha, hb]

include 𝒜 in
theorem span_singleton_isHomogeneous {m : M} {e : ℤ} (hm : m ∈ ℳ e) :
    (Submodule.span A {m}).IsHomogeneous ℳ := by
  intro d x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [homogeneous_smul_component 𝒜 ℳ hm]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m)

omit [Algebra R A] in
theorem sup_isHomogeneous {P Q : Submodule A M}
    (hP : P.IsHomogeneous ℳ) (hQ : Q.IsHomogeneous ℳ) :
    (P ⊔ Q).IsHomogeneous ℳ := by
  intro d x hx
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
  rw [decompose_add]
  exact Submodule.add_mem _ ((show P ≤ P ⊔ Q from le_sup_left) (hP d hp))
    ((show Q ≤ P ⊔ Q from le_sup_right) (hQ d hq))

def relativeAnnihilator (P : Submodule A M) (m : M) : Ideal A :=
  P.comap (LinearMap.toSpanSingleton A M m)

theorem relativeAnnihilator_isHomogeneous (P : Submodule A M)
    (hP : P.IsHomogeneous ℳ) {m : M} {e : ℤ} (hm : m ∈ ℳ e) :
    (relativeAnnihilator P m).IsHomogeneous 𝒜 := by
  intro d a ha
  change (decompose 𝒜 a d).val • m ∈ P
  have h := hP (d + e) ha
  change (decompose ℳ (a • m) (d + e)).val ∈ P at h
  rw [homogeneous_smul_component 𝒜 ℳ hm, add_sub_cancel_right] at h
  exact h

omit [Algebra R A] in
theorem exists_homogeneous_not_mem {P : Submodule A M} (hP : P ≠ ⊤) :
    ∃ (m : M) (d : ℤ), m ∈ ℳ d ∧ m ∉ P := by
  classical
  by_contra h
  push Not at h
  apply hP
  apply top_unique
  intro m _
  rw [← sum_support_decompose ℳ m]
  apply Submodule.sum_mem
  intro d _
  exact h _ d (decompose ℳ m d).property

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicSubmodule
