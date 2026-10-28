import Mathlib.RingTheory.Etale.StandardEtale

/-! # Section Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionKernel

noncomputable section

/-! A section of an étale algebra is isolated by an actual principal
open. The chosen element maps to one and annihilates the section kernel. -/

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  [Algebra.Etale R A] (ε : A →ₐ[R] R)

theorem exists_annihilator :
    ∃ s : A, ε s = 1 ∧ ∀ x, ε x = 0 → s * x = 0 := by
  have hsurj : Function.Surjective ε := fun r => ⟨algebraMap R A r, ε.commutes r⟩
  let : Algebra A R := ε.toAlgebra
  let : IsScalarTower R A R := .of_algebraMap_eq' ε.comp_algebraMap.symm
  have hform : Algebra.FormallyEtale A R := .of_restrictScalars (R := R)
  have hid : IsIdempotentElem (RingHom.ker ε.toRingHom) :=
    (Algebra.FormallyEtale.iff_of_surjective (show Function.Surjective (algebraMap A R) from hsurj)).mp hform
  obtain ⟨e, he, hker⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg (RingHom.ker ε.toRingHom)
      (Algebra.FinitePresentation.ker_fG_of_surjective ε hsurj)).mp hid
  have hker' : RingHom.ker ε.toRingHom = Ideal.span {e} := hker
  have heval : ε e = 0 := by
    change e ∈ RingHom.ker ε.toRingHom
    rw [hker']
    exact Ideal.subset_span (Set.mem_singleton e)
  refine ⟨1 - e, by simp only [map_sub, map_one, heval, sub_zero], ?_⟩
  intro x hx
  have hmem : x ∈ Ideal.span {e} := by
    rw [← hker']
    exact hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
  calc
    (1 - e) * (a * e) = a * ((1 - e) * e) := by ring
    _ = 0 := by rw [sub_mul, one_mul, he.eq, sub_self, mul_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionKernel
