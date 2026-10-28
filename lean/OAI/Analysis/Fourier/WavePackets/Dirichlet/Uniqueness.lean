import OAI.Analysis.Fourier.WavePackets.PeriodicDirichletAssembly
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Barriers

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Concentration
open scoped ContDiff

/-- Uniqueness for the manuscript's three-slot equation, on the entire
closed fiber. Global extensions outside the domain need not coincide. -/
theorem PeriodicQuaternionicSolution.threeSlot_eq_on_closed
    {m : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b}
    (S T : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 → S.u x = T.u x := by
  intro x hx
  have h := S.padFourth.eq_on_closed T.padFourth (insertFourth m x)
    (by simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,dropFourth_insertFourth] using hx)
  simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicSolution.padFourth,dropFourth_insertFourth] using h

end OAI.Analysis.Fourier.WavePackets
