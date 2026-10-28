import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygyGraphEquations

/-! # Syzygy Graph Projection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygyGraphProjection.GradedHilbert

noncomputable section

/-! Removing the auxiliary graph variable preserves the elimination relations and their weighted degree bounds. -/

open _root_.MvPolynomial

variable {K σ ι : Type*} [Field K]

def syzygyVariableEmbedding : ι ⊕ σ → ι ⊕ Option σ := Sum.map id some

theorem syzygyVariableEmbedding_injective :
    Function.Injective (syzygyVariableEmbedding (ι := ι) (σ := σ)) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => simpa [syzygyVariableEmbedding] using h
    | inr y => simp [syzygyVariableEmbedding] at h
  | inr x =>
    cases y with
    | inl y => simp [syzygyVariableEmbedding] at h
    | inr y => simpa [syzygyVariableEmbedding] using h

def syzygyGraphProjection : MvPolynomial (ι ⊕ Option σ) K →ₐ[K] MvPolynomial (ι ⊕ σ) K :=
  killCompl syzygyVariableEmbedding_injective

theorem syzygyGraphProjection_rename (p : MvPolynomial (ι ⊕ σ) K) :
    syzygyGraphProjection (rename syzygyVariableEmbedding p) = p :=
  killCompl_rename_app syzygyVariableEmbedding_injective p

theorem syzygy_rename_supported (p : MvPolynomial (ι ⊕ σ) K) :
    rename syzygyVariableEmbedding p ∈ supported K ({Sum.inr none}ᶜ : Set (ι ⊕ Option σ)) := by
  rw [mem_supported]
  intro i hi
  obtain ⟨j, _, rfl⟩ := mem_vars_rename syzygyVariableEmbedding p hi
  cases j <;> simp [syzygyVariableEmbedding]

theorem syzygy_rename_projection (p : MvPolynomial (ι ⊕ Option σ) K)
    (hp : p ∈ supported K ({Sum.inr none}ᶜ : Set (ι ⊕ Option σ))) :
    rename syzygyVariableEmbedding (syzygyGraphProjection p) = p := by
  have hv : (p.vars : Set (ι ⊕ Option σ)) ⊆ Set.range syzygyVariableEmbedding := by
    intro i hi
    cases i with
    | inl i => exact ⟨Sum.inl i, rfl⟩
    | inr i =>
      cases i with
      | none => exact False.elim ((mem_supported.mp hp) hi (Set.mem_singleton _))
      | some i => exact ⟨Sum.inr i, rfl⟩
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p syzygyVariableEmbedding
    syzygyVariableEmbedding_injective hv
  rw [syzygyGraphProjection_rename]

theorem syzygyGraphProjection_weighted_homogeneous
    {p : MvPolynomial (ι ⊕ Option σ) K} {N d : ℕ}
    (hp : p.IsWeightedHomogeneous (SyzygyGraphEquations.GradedHilbert.syzygyGraphWeight N) d) :
    (syzygyGraphProjection p).IsWeightedHomogeneous
      (Sum.elim (fun _ : ι => N + 1) (fun _ : σ => 1)) d := by
  intro a ha
  change (killCompl syzygyVariableEmbedding_injective p).coeff a ≠ 0 at ha
  rw [coeff_killCompl] at ha
  have hd := hp ha
  rw [WeightedRename.GradedHilbert.naturalWeight_mapDomain] at hd
  have hw : SyzygyGraphEquations.GradedHilbert.syzygyGraphWeight (ι := ι) (σ := σ) N ∘ syzygyVariableEmbedding =
      Sum.elim (fun _ : ι => N + 1) (fun _ : σ => 1) := by
    funext i
    cases i <;> rfl
  rwa [hw] at hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygyGraphProjection.GradedHilbert
