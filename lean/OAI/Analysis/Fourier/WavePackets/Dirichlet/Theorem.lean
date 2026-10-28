import OAI.Analysis.Fourier.WavePackets.Dirichlet.Existence
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Uniqueness

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet

/-- Existence, uniqueness on the closed fiber, and the two defining-
function barriers for the manuscript's three-slot Dirichlet problem. -/
theorem periodic_quaternionic_dirichlet
    {m : ℕ} {P V ι : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b) :
    ∃ (S : PeriodicQuaternionicSolution D) (B c : ℝ),
      0 < c ∧ c ≤ B ∧
      (∀ x, D.defining x ≤ 0 →
        B * D.defining x ≤ S.u x ∧ S.u x ≤ c * D.defining x) ∧
      (∀ T : PeriodicQuaternionicSolution D, ∀ x,
        D.defining x ≤ 0 → T.u x = S.u x) := by
  obtain ⟨S⟩ := threeSlotDirichletExistence D
  obtain ⟨B,c,hc,hcB,hbar⟩ := D.threeSlot_barriers
  exact ⟨S,B,c,hc,hcB,hbar S,fun T => T.threeSlot_eq_on_closed S⟩

/-- The four-slot version has the same source-level conclusion. -/
theorem fourSlot_periodic_quaternionic_dirichlet
    {m : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    ∃ (S : PeriodicQuaternionicSolution D) (B c : ℝ),
      0 < c ∧ c ≤ B ∧
      (∀ x, D.defining x ≤ 0 →
        B * D.defining x ≤ S.u x ∧ S.u x ≤ c * D.defining x) ∧
      (∀ T : PeriodicQuaternionicSolution D, ∀ x,
        D.defining x ≤ 0 → T.u x = S.u x) := by
  obtain ⟨S⟩ := D.nonempty_solution
  obtain ⟨B,c,hc,hcB,hbar⟩ := D.fourSlot_barriers
  exact ⟨S,B,c,hc,hcB,hbar S,fun T => T.eq_on_closed S⟩

end OAI.Analysis.Fourier.WavePackets
