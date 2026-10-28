import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Family
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Descent

/-! Genuine solution comparison is insensitive to the chosen extension
of the defining function away from the closed physical domain. -/
noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}

theorem PeriodicQuaternionicSolution.eq_on_closed_of_same_data
    {D D' : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}
    (S : PeriodicQuaternionicSolution D) (S' : PeriodicQuaternionicSolution D')
    (hi : ∀ x, D'.defining x < 0 ↔ D.defining x < 0)
    (hc : ∀ x, D'.defining x ≤ 0 ↔ D.defining x ≤ 0)
    (hB : D'.background = D.background)
    (hF : ∀ x, D.defining x < 0 → D'.density x = D.density x) :
    ∀ x, D.defining x ≤ 0 → S'.u x = S.u x := by
  have hz (x) (hx : D.defining x = 0) : D'.defining x = 0 := by
    apply le_antisymm ((hc x).mpr hx.le)
    by_contra hn
    have hn' : D'.defining x < 0 := lt_of_not_ge hn
    have := (hi x).mp hn'
    linarith
  have hh := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice D.dimension e b D.compact
    ((D.background_smooth.add S'.smooth).of_le (by simp)).contDiffOn
    ((D.background_smooth.add S.smooth).of_le (by simp)).contDiffOn
    (D.defining_smooth.of_le (by simp))
    (D.background_smooth.continuous.add S'.smooth.continuous).continuousOn
    (D.background_smooth.continuous.add S.smooth.continuous).continuousOn
    D.bounded D.defining_periodic (D.background_periodic.add S'.periodic)
    (D.background_periodic.add S.periodic)
    (fun x hx ↦ D.defining_positive x hx.le)
    (fun x hx ↦ by simpa only [hB] using S'.admissible x ((hi x).mpr hx))
    S.admissible
    (fun x hx ↦ by
      rw [← hB, S'.equation x ((hi x).mpr hx), hB, S.equation x hx, hF x hx])
    (fun x hx ↦ by rw [S'.boundary x (hz x hx), S.boundary x hx])
  intro x hx
  exact add_left_cancel (hh x hx)

end OAI.Analysis.Fourier.WavePackets
