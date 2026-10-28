import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseFiniteProjectiveFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Normalization

/-! # Indexed Projective Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedProjectiveFrames

noncomputable section

/-! A projective frame chosen from a finite labeled configuration can
be indexed by the prescribed rank, retaining the actual selected labels. -/
open scoped Classical
universe u v
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {ι : Type v} (e : ι → V) {r : ℕ}

def HasFiniteIndexedProjectiveFrame : Prop :=
  ∃ (b : Module.Basis (Fin r) K V) (σ : Fin r → ι),
    (∀ k, b k = e (σ k)) ∧ ∃ j : ι, ∀ k, b.repr (e j) k ≠ 0

omit [Module.Finite K V] in
theorem hasFiniteIndexedProjectiveFrame_of_basis
    (hr : Module.finrank K V = r)
    (h : ∃ (κ : Type u) (_ : Fintype κ) (b : Module.Basis κ K V),
      Set.range b ⊆ Set.range e ∧ ∃ j : ι, ∀ k, b.repr (e j) k ≠ 0) :
    HasFiniteIndexedProjectiveFrame (K := K) (r := r) e := by
  obtain ⟨κ, hκ, b, hb, j, hj⟩ := h
  let : Fintype κ := hκ
  have hc : Fintype.card κ = r := (Module.finrank_eq_card_basis b).symm.trans hr
  let q : κ ≃ Fin r := (Fintype.equivFin κ).trans (finCongr hc)
  let c := b.reindex q
  have he (k : Fin r) : ∃ i : ι, e i = c k := hb ⟨q.symm k, by simp [c]⟩
  choose σ hσ using he
  exact ⟨c, σ, fun k => (hσ k).symm, j, fun k => by
    simpa only [c, Module.Basis.repr_reindex_apply] using hj (q.symm k)⟩

omit [Module.Finite K V] in
theorem HasFiniteIndexedProjectiveFrame.selected_labels_injective
    (b : Module.Basis (Fin r) K V) (σ : Fin r → ι) (hb : ∀ k, b k = e (σ k)) :
    Function.Injective σ := by
  intro i j hij
  apply b.injective
  rw [hb, hb, hij]

omit [Module.Finite K V] in
theorem HasFiniteIndexedProjectiveFrame.normalization
    (h : HasFiniteIndexedProjectiveFrame (K := K) (r := r) e) :
    ∃ (f : V ≃ₗ[K] (Fin r → K)) (σ : Fin r → ι) (j : ι),
      Function.Injective σ ∧ f (e j) = (fun _ => 1) ∧
      ∀ i : Fin r, ∃ c : K, c ≠ 0 ∧
        ∀ k : Fin r, f (e (σ i)) k = if i = k then c else 0 := by
  obtain ⟨b, σ, hb, j, hj⟩ := h
  let hu := fun k => isUnit_iff_ne_zero.mpr (hj k)
  let f := ProjectiveFrame.Normalization.projectiveFrameNormalization b (e j) hu
  refine ⟨f, σ, j, HasFiniteIndexedProjectiveFrame.selected_labels_injective e b σ hb,
    ProjectiveFrame.Normalization.projectiveFrameNormalization_additional b (e j) hu, ?_⟩
  intro i
  refine ⟨↑((hu i).unit⁻¹), Units.ne_zero _, fun k => ?_⟩
  rw [← hb i, ProjectiveFrame.Normalization.projectiveFrameNormalization_basis]
  by_cases hik : i = k
  · subst k
    simp only
  · simp only [hik, ite_false]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedProjectiveFrames
