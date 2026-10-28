import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.AffineNeighborhood

/-! # Constrained Linear Forms -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ConstrainedLinearForms

noncomputable section

/-! Homogeneous linear forms can avoid both finitely many projective
point ideals and finitely many additional proper linear subspaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def pointSubmodule (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) : Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :=
  (x.asHomogeneousIdeal.toIdeal.restrictScalars ℂ).comap (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1).subtype

theorem pointSubmodule_ne_top (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) : pointSubmodule n x ≠ ⊤ := by
  obtain ⟨j, hj⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n x
  rw [Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen] at hj
  intro he
  have h : (⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X ℂ j⟩ : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) ∈
      pointSubmodule n x := by rw [he]; trivial
  exact hj h

theorem exists_form (n : ℕ) {ι κ : Type} [Finite ι] [Finite κ]
    (x : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (N : κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)) (hN : ∀ j, N j ≠ ⊤) :
    ∃ p : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1, (∀ i, p.val ∉ (x i).asHomogeneousIdeal) ∧ ∀ j, p ∉ N j := by
  let F : ι ⊕ κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) := Sum.elim (fun i => pointSubmodule n (x i)) N
  have hF : ∀ j, F j ≠ ⊤ := by
    intro j
    cases j with
    | inl i => exact pointSubmodule_ne_top n (x i)
    | inr j => exact hN j
  obtain ⟨p, hp⟩ := Submodule.exists_forall_notMem_of_forall_ne_top F hF
  exact ⟨p, fun i => hp (Sum.inl i), fun j => hp (Sum.inr j)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ConstrainedLinearForms
