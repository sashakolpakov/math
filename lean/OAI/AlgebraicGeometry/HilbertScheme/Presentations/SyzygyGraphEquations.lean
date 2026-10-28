import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphSubstitutionIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.VariableElimination

/-! # Syzygy Graph Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygyGraphEquations.GradedHilbert

noncomputable section

/-! Bounded elimination for the graph equations Yᵢ − gᵢt of a homogeneous polynomial family. -/

open _root_.MvPolynomial

universe u v z

variable {K : Type u} [Field K] {σ : Type v} {ι : Type z}

def syzygyGraphData (g : ι → MvPolynomial σ K) (i : ι) : MvPolynomial (Option σ) K :=
  rename some (g i) * X none

def syzygyGraphWeight (N : ℕ) : ι ⊕ Option σ → ℕ :=
  Sum.elim (fun _ => N + 1) (fun _ => 1)

theorem syzygyGraphWeight_pos (N : ℕ) (i : ι ⊕ Option σ) :
    syzygyGraphWeight N i ≠ 0 := by
  cases i <;> simp [syzygyGraphWeight]

theorem syzygyGraphEquation_weighted_homogeneous
    (g : ι → MvPolynomial σ K) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (i : ι) :
    (GraphSubstitutionIdeal.GradedHilbert.graphEquation (syzygyGraphData g) i).IsWeightedHomogeneous (syzygyGraphWeight N) (N + 1) := by
  apply (isWeightedHomogeneous_X K (syzygyGraphWeight N) (Sum.inl i)).sub
  apply WeightedRename.GradedHilbert.weightedHomogeneous_rename (syzygyGraphWeight N) Sum.inr
  have hrename : (rename some (g i)).IsWeightedHomogeneous (fun _ : Option σ => 1) N := by
    apply WeightedRename.GradedHilbert.weightedHomogeneous_rename (fun _ : Option σ => 1) some
    exact hg i
  exact hrename.mul (isWeightedHomogeneous_X K (fun _ : Option σ => 1) none)

theorem exists_bounded_syzygy_graph_elimination
    [Fintype ι] {n : ℕ} (E : (ι ⊕ Option σ) ≃ Fin (n + 1))
    (g : ι → MvPolynomial σ K) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    ∃ B : Finset (MvPolynomial (ι ⊕ Option σ) K),
      (∀ f ∈ B, GraphSubstitutionIdeal.GradedHilbert.graphSubstitution (syzygyGraphData g) f = 0 ∧ f ≠ 0 ∧
        f ∈ supported K ({Sum.inr none}ᶜ : Set (ι ⊕ Option σ)) ∧
        ∃ d ≤ Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n (N + 1),
          f.IsWeightedHomogeneous (syzygyGraphWeight N) d) ∧
      ∀ f ∈ supported K ({Sum.inr none}ᶜ : Set (ι ⊕ Option σ)),
        GraphSubstitutionIdeal.GradedHilbert.graphSubstitution (syzygyGraphData g) f = 0 ↔
          f ∈ Ideal.span (B : Set (MvPolynomial (ι ⊕ Option σ) K)) := by
  classical
  obtain ⟨B, hB, hgen⟩ := Finite.VariableElimination.GradedHilbert.exists_weighted_elimination_generators_of_equiv E
    (syzygyGraphWeight N) (syzygyGraphWeight_pos N) {Sum.inr none}
    (GraphSubstitutionIdeal.GradedHilbert.graphEquation (syzygyGraphData g)) (fun _ => N + 1)
    (syzygyGraphEquation_weighted_homogeneous g N hg)
    (GraphSubstitutionIdeal.GradedHilbert.graphEquation_ne_zero (syzygyGraphData g)) (N + 1) (fun _ => le_rfl)
  simp only [Finset.coe_singleton] at hB hgen
  have hker (f : MvPolynomial (ι ⊕ Option σ) K) :
      f ∈ Ideal.span (Set.range (GraphSubstitutionIdeal.GradedHilbert.graphEquation (syzygyGraphData g))) ↔
        GraphSubstitutionIdeal.GradedHilbert.graphSubstitution (syzygyGraphData g) f = 0 := by
    rw [← GraphSubstitutionIdeal.GradedHilbert.graphSubstitution_kernel, RingHom.mem_ker]
    rfl
  refine ⟨B, ?_, ?_⟩
  · intro f hf
    obtain ⟨hfi, hf0, hfs, d, hd, hhom⟩ := hB f hf
    exact ⟨(hker f).mp hfi, hf0, hfs, d, hd, hhom⟩
  · intro f hfs
    exact (hker f).symm.trans (hgen f hfs)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygyGraphEquations.GradedHilbert
