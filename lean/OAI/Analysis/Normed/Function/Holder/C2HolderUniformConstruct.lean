import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

open Set Module
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.Analysis.PDE.Dirichlet

/-- A uniform bound on actual jets produces a uniformly bounded family
in the genuine complete C²,α space. -/
theorem exists_uniform_C2Holder {E F J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) {α N : ℝ}
    (hα : 0 ≤ α) (hN : 0 ≤ N) (f : J → E → F)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (h₀ : ∀ i x, x ∈ K → ‖f i x‖ ≤ N)
    (h₁ : ∀ i x, x ∈ K → ‖fderiv ℝ (f i) x‖ ≤ N)
    (h₂ : ∀ i x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ N)
    (hh : ∀ i x, x ∈ K → ∀ y, y ∈ K →
      ‖fderiv ℝ (fderiv ℝ (f i)) x - fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ N * (dist x y) ^ α) :
    ∃ Φ : J → C2Holder (F := F) hΩK α, ∀ i, ‖Φ i‖ ≤ N ∧
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ i) x = f i x) ∧
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ i) x = fderiv ℝ (f i) x) ∧
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ i) x = fderiv ℝ (fderiv ℝ (f i)) x) := by
  let Φ := fun i ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff hΩ hΩK hα (f i) (hf i) (h₀ i) (h₁ i) (h₂ i) (hh i)
  refine ⟨Φ, fun i ↦ ⟨?_, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα hN
  · intro x; exact h₀ i x x.property
  · intro x; exact h₁ i x x.property
  · intro x; exact h₂ i x x.property
  · intro x y; exact hh i x x.property y y.property

theorem latticePeriodic_of_value_eq {E P V F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (hK : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ x ∈ K))
    (u : C2Holder (F := F) hΩK α) (f : E → F)
    (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) (hu : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value u x = f x) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u)) := by
  intro x l
  let y := e.symm ((e x).1 + (l : P), (e x).2)
  have hy : y ∈ K ↔ x ∈ K := Iff.of_eq (hK x l)
  by_cases hx : x ∈ K
  · change boundedZeroExtension _ y = boundedZeroExtension _ x
    rw [boundedZeroExtension_apply _ (hy.mpr hx), boundedZeroExtension_apply _ hx, hu, hu]
    exact hf x l
  · have hy' : y ∉ K := fun h ↦ hx (hy.mp h)
    change boundedZeroExtension _ y = boundedZeroExtension _ x
    simp only [boundedZeroExtension, OAI.Analysis.PDE.Dirichlet.zeroExtend, dite_eq_right hx, dite_eq_right hy']

end OAI.Analysis.Normed.Function.Holder
