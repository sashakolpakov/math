import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! # Complement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Complement

noncomputable section

/-! A positive summand detects its orthogonal complementary summand.
Thus a Hermitian isometry carrying the positive summand onto the
positive summand also carries their complements into each other. -/

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mem_complement_of_orthogonal
    (F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (P Q : Submodule ℂ V) (hPQ : IsCompl P Q)
    (hpos : ∀ p ∈ P, p ≠ 0 → 0 < (F p p).re)
    (horth : ∀ p ∈ P, ∀ q ∈ Q, F p q = 0)
    (v : V) (hv : ∀ p ∈ P, F p v = 0) : v ∈ Q := by
  obtain ⟨p, q, hpq, _⟩ := Submodule.existsUnique_add_of_isCompl hPQ v
  have hz := hv p p.property
  rw [← hpq, map_add, horth p p.property q q.property, add_zero] at hz
  have hp : (p : V) = 0 := by
    by_contra hp
    have h := hpos p p.property hp
    rw [hz, Complex.zero_re] at h
    exact (lt_irrefl 0) h
  rw [← hpq, hp, zero_add]
  exact q.property

theorem hermitianMap_complement
    (F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (G : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ)
    (P Q : Submodule ℂ V) (P' Q' : Submodule ℂ W) (hP'Q' : IsCompl P' Q')
    (hpos : ∀ p ∈ P', p ≠ 0 → 0 < (G p p).re)
    (horth : ∀ p ∈ P, ∀ q ∈ Q, F p q = 0)
    (horth' : ∀ p ∈ P', ∀ q ∈ Q', G p q = 0)
    (f : V →ₗ[ℂ] W) (hf : ∀ x y, G (f x) (f y) = F x y)
    (hP : ∀ p' ∈ P', ∃ p ∈ P, f p = p')
    (q : V) (hq : q ∈ Q) : f q ∈ Q' := by
  apply mem_complement_of_orthogonal G P' Q' hP'Q' hpos horth'
  intro p' hp'
  obtain ⟨p, hp, rfl⟩ := hP p' hp'
  exact (hf p q).trans (horth p hp q hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Complement
