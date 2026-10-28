import OAI.Analysis.Fourier.WavePackets.Dirichlet.Padding
import OAI.Analysis.PDE.Dirichlet.Periodic.Barriers

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Concentration

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The source's two scalar barriers, with constants determined by the
fixed data before any solution is selected. Empty fibers are included. -/
theorem PeriodicQuaternionicData.fourSlot_barriers
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ S : PeriodicQuaternionicSolution D,
      ∀ x, D.defining x ≤ 0 → B*D.defining x ≤ S.u x ∧ S.u x ≤ c*D.defining x := by
  by_cases hne : {x | D.defining x ≤ 0}.Nonempty
  · obtain ⟨c,B,hc,hcB,hbounds⟩ := OAI.Analysis.PDE.Dirichlet.uniform_dirichlet_solution_barriers_lattice D.dimension
      e b D.compact hne (D.background_smooth.of_le (by simp))
      (D.defining_smooth.of_le (by simp)) D.density D.density_smooth.continuous
      D.bounded D.background_periodic D.defining_periodic D.density_periodic
      D.background_nonnegative D.defining_positive D.background_degenerate D.density_positive
    exact ⟨B,c,hc,hcB,fun S => hbounds S.u (S.smooth.of_le (by simp)) S.periodic
      S.admissible S.equation S.boundary⟩
  · refine ⟨1,1,by norm_num,le_rfl,fun S x hx => ?_⟩
    exact False.elim (hne ⟨x,hx⟩)

/-- An existing three-slot solution can itself be padded by an unused
fourth real coordinate, not only obtained by descent from a padded solve. -/
def PeriodicQuaternionicSolution.padFourth
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b} (S : PeriodicQuaternionicSolution D) :
    PeriodicQuaternionicSolution D.padFourth where
  u x := S.u (dropFourth m x)
  smooth := S.smooth.comp (dropFourth m).contDiff
  periodic := latticePeriodic_dropFourth e b S.periodic
  boundary x hx := S.boundary _ hx
  admissible x hx := by
    change (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      (fun y => D.background (dropFourth m y)+S.u (dropFourth m y)) x)).PosDef
    rw [quaternionHessian_dropFourth ((D.background_smooth.add S.smooth).of_le (by simp))]
    exact S.admissible _ hx
  equation x hx := by
    change OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      (fun y => D.background (dropFourth m y)+S.u (dropFourth m y)) x) =
        D.density (dropFourth m x)
    rw [quaternionHessian_dropFourth ((D.background_smooth.add S.smooth).of_le (by simp))]
    exact S.equation _ hx

/-- The manuscript's three-slot Dirichlet problem has the same genuine
uniform barriers after padding and then evaluating at zero fourth coordinate. -/
theorem PeriodicQuaternionicData.threeSlot_barriers
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b) :
    ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ S : PeriodicQuaternionicSolution D,
      ∀ x, D.defining x ≤ 0 → B*D.defining x ≤ S.u x ∧ S.u x ≤ c*D.defining x := by
  obtain ⟨B,c,hc,hcB,hbounds⟩ := D.padFourth.fourSlot_barriers
  refine ⟨B,c,hc,hcB,fun S x hx => ?_⟩
  have h := hbounds S.padFourth (insertFourth m x)
    (by simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,dropFourth_insertFourth] using hx)
  simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicSolution.padFourth,
    dropFourth_insertFourth] using h

end OAI.Analysis.Fourier.WavePackets
